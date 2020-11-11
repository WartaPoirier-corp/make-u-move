#![deny(missing_docs)]

//! A crate to parse simple Makefiles.
//!
//! A lot of features are not supported (yet), but
//! the most common ones should work.
//!
//! The main entry point for parsing a Makefile is
//! [`Makefile::try_parse`].
//!
//! [`Makefile::try_parse`]: ./struct.Makefile.html#method.try_parse

/// A parsed Makefile
#[derive(Clone, Debug, PartialEq)]
pub struct Makefile {
    /// The set of explicit rules in this Makefile.
    rules: Vec<Rule>,
    /// The set of vars defined in this Makefile
    vars: Vars,
}

/// A rule defined in a Makefile
///
/// ```make
/// name: dep1 dep2 dep3
///     command 1
///     command 2
///     command 3
/// ```
#[derive(Clone, Debug, PartialEq)]
pub struct Rule {
    /// The name of the rule
    ///
    /// It never contains `%` or variables even if its definition
    /// in the Makefile was using them.
    pub name: String,
    /// The dependencies of this rule
    pub deps: Vec<RuleRef>,
    /// The recipe for this rule
    pub commands: Vec<String>,
}

/// A reference to a rule.
///
/// If we know exactly what rule was referenced, it will be considered
/// to be "resolved", otherwise it is "unresolved" and the name
/// is kept as it was in the Makefile.
#[derive(Debug, Clone, PartialEq)]
pub enum RuleRef {
    /// A rule reference that has not been resolved yet.
    /// 
    /// It may be a file name required by another rule in order to build,
    /// that has no rules on how to build it.
    Unresolved(String),
    /// A well-defined reference to another rule.
    ///
    /// The wrapped value is the index of the referenced rule in the Makefile, which
    /// may be obtained with the [`get_rule_at`] method.
    ///
    /// [`get_rule_at`]: struct.Makefile.html#method.get_rule_at
    Resolved(usize),
}

/// Errors that may happen during Makefile parsing
#[derive(Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Error {
    /// # Example Makefile triggering this error
    ///
    /// ```make
    ///     echo "Error !"
    /// ```
    CommandOutsideOfRule,
}

/// Iterator over logical lines of a text
///
/// Makefile are read by logical lines and not by physical lines :
/// if a line-break is prefixed by a backslash, the next line is considered
/// to be a continuation of the current line.
struct LogicalLines<'a> {
    text: &'a str,
}

/// Iterates avoir the logical lines of [`text`].
fn logical_lines_of<'a>(text: &'a str) -> LogicalLines<'a> {
    LogicalLines { text }
}

impl<'a> Iterator for LogicalLines<'a> {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        while self.text.starts_with('\n') {
            self.text = &self.text[1..];
        }

        if let Some(mut index_of_eol) = self.text.find('\n') {
            while index_of_eol > 0 && self.text[index_of_eol - 1..index_of_eol] == *"\\" {
                if let Some(new_index) = self.text[index_of_eol+1..].find('\n') {
                    index_of_eol += new_index;
                } else {
                    index_of_eol = self.text.len() - 1
                }
            }

            let (line, remaining) = self.text.split_at(index_of_eol + 1);
            self.text = remaining;
            Some(line
                 .replace("\\\n", "\n")
                 .lines()
                 .enumerate()
                 .map(|(i, l)| if i > 0 { l.trim_start() } else { l })
                 .collect::<Vec<_>>()
                 .join(" ")
            )
        } else if !self.text.is_empty() {
            let res = self.text.to_owned();
            self.text = "";
            Some(res)
        } else {
            None
        }
    }
}

/// A variable in a Makefile
///
/// Depending on the operator used to define it,
/// it may be "immediate" or "deferred".
#[derive(Clone, Debug, PartialEq)]
enum Var {
    /// This variable is fully expanded using the context at its definition point
    Immediate(String),
    /// This variable is expanded as late as possible, and needs to be re-expanded every time
    /// it is used, with the current context
    Deferred(String),
}

/// A collection of variables
#[derive(Clone, Debug, PartialEq)]
struct Vars {
    /// The collection of variables : names associated to values
    inner: std::collections::HashMap<String, Var>,
}

impl Default for Vars {
    fn default() -> Self {
        // TODO: there are more than these
        use Var::Immediate as I;
        let mut inner = std::collections::HashMap::new();
        inner.insert("CC".into(), I("cc".into()));
        inner.insert("CFLAGS".into(), I("".into()));
        inner.insert("LDFLAGS".into(), I("".into()));
        inner.insert("LDLIBS".into(), I("".into()));
        inner.insert("CXX".into(), I("g++".into()));
        Vars { inner }
    }
}

impl Vars {
    /// Expand variables in a line.
    ///
    /// # Parameters
    ///
    /// - `immediate_only`: indicates if only immediate variables must be expanded. If it is not
    ///   enabled, we can tell that all $ are undefined variables, and thus all un-expanded
    ///   variables will be removed at the end of this function in this case.
    /// - `line`: the line of text to expand, which will be modified by this function.
    fn expand_line<'a>(&'a self, immediate_only: bool, line: &mut String) {
        for (var, val) in self.inner.iter() {
            match val {
                Var::Deferred(_) if immediate_only => {},
                Var::Immediate(to_exp) | Var::Deferred(to_exp) => {
                    *line = line.replace(&format!("$({})", var), &to_exp);
                }
            }
        }

        // remove un-expanded variables
        if !immediate_only {
            let mut start_idx = 0;
            dbg!(&line);
            while let Some(dollar_idx) = line[start_idx..].find('$') {
                if dbg!(&line[dollar_idx + 1..dollar_idx + 2]) != "(" {
                    start_idx = dollar_idx + 1;
                    continue;
                }

                if let Some(end) = line[dollar_idx..].find(')') {
                    line.replace_range(start_idx + dollar_idx..start_idx + dollar_idx + end + 1, "");
                }
            }
        }

        *line = line.trim().to_owned();
    }
}

impl Makefile {
    /// Tries to read a Makefile
    ///
    /// # Parameters
    ///
    /// - `src`: the contents of the Makefile
    pub fn try_parse(src: &str) -> Result<Makefile, Error> {
        let mut makefile = Makefile { rules: Vec::new(), vars: Vars::default(), };
        let mut current_rule: Option<Rule> = None;
        for line in logical_lines_of(src) {
            if let Some(line) = line.splitn(1, '#').next() {
                if !line.is_empty() {
                    if line.starts_with('\t') {
                        match current_rule {
                            Some(ref mut rule) => {
                                rule.commands.push(line.trim().to_owned());
                            },
                            None => return Err(Error::CommandOutsideOfRule)
                        }
                    } else {
                        let mut line = line.to_owned();
                        makefile.vars.expand_line(true, &mut line);
                        let _define = line.starts_with("define ");
                        
                        // TODO:
                        /*if let Some(index) = line.find("::=") { // Simple POSIX assign
                            let (name, val) = line.split_at(index);
                            let mut name = name.trim().to_owned();
                            makefile.vars.expand_line(false, &mut name);
                            let val = val.trim().to_owned();
                            makefile.vars.inner.insert(name, Var::Deferred(val));
                        } else if let Some(index) = line.find(":=") { // Simple assign
                            let (name, val) = line.split_at(index);
                            let mut name = name.trim().to_owned();
                            vars.expand_line(false, &mut name);
                            let val = val.trim().to_owned();
                            vars.inner.insert(name, Var::Deferred(val));
                        } else if let Some(index) = line.find("?=") { // Conditional assign
                            let (name, val) = line.split_at(index);
                            let mut name = name.trim().to_owned();
                            vars.expand_line(false, &mut name);
                            let val = val.trim().to_owned();
                            vars.inner.insert(name, Var::Deferred(val));
                        } else if let Some(index) = line.find("+=") { // Append assign
                            let (name, val) = line.split_at(index);
                            let mut name = name.trim().to_owned();
                            vars.expand_line(false, &mut name);
                            let val = val.trim().to_owned();
                            vars.inner.insert(name, Var::Deferred(val));
                        } else if let Some(index) = line.find("!=") { // Shell assign
                            let (name, val) = line.split_at(index);
                            let mut name = name.trim().to_owned();
                            vars.expand_line(false, &mut name);
                            let val = val.trim().to_owned();
                            vars.inner.insert(name, Var::Deferred(val));
                        } else */if let Some(index) = line.find("=") { // Recursive assign
                            let (name, val) = line.split_at(index);
                            let mut name = name.trim().to_owned();
                            makefile.vars.expand_line(false, &mut name);
                            let val = val[1..].trim().to_owned();
                            makefile.vars.inner.insert(name, Var::Deferred(val));
                        } else if let Some(index) = line.find(":") { // Rule
                            let (name, rest) = line.split_at(index);
                            let mut name = name.trim().to_owned();
                            makefile.vars.expand_line(false, &mut name);
                            let mut rest_split = rest[1..].split(';');
                            let deps = rest_split.next().unwrap()
                                .split(' ')
                                .filter_map(|x| {
                                    let x = x.trim().to_owned();
                                    if !x.is_empty() {
                                        Some(RuleRef::Unresolved(x))
                                    } else {
                                        None
                                    }
                                }).collect();
                            let commands = if let Some(cmd) = rest_split.next() {
                                vec![ cmd.trim().to_owned() ]
                            } else {
                                Vec::new()
                            };
                            if let Some(prev_rule) = current_rule.replace(Rule {
                                name,
                                deps,
                                commands,
                            }) {
                                makefile.rules.push(prev_rule);
                            }
                        } else if line == "endef" {
                            todo!()
                        }
                    }
                }
            }
        }

        if let Some(rule) = current_rule {
            makefile.rules.push(rule)
        }

        makefile.resolve_deps();

        Ok(makefile)
    }

    /// Transform as much "unresolved" dependencies into "resolved" ones, by looking
    /// for matching rules in the set of rules of the Makefile.
    fn resolve_deps(&mut self) {
        let self_clone = self.clone();
        for ref mut rule in self.rules.iter_mut() {
            for ref mut dep in rule.deps.iter_mut() {
                match dep {
                    RuleRef::Unresolved(name) => if let Some(other) = self_clone.get_rule_index(name) {
                        **dep = RuleRef::Resolved(other);
                    },
                    _ => {}
                }
            }
        }
    }

    /// Returns the index of a rule with a given name in the list of rules
    fn get_rule_index(&self, name: &str) -> Option<usize> {
        self.rules.iter().position(|r| r.name == name)
    }

    /// Get the rules at a given index
    ///
    /// Does not expand the variables in the recipe.
    /// Only explicitely defined rules may be accessed this way.
    pub fn get_rule_at(&self, index: usize) -> Option<Rule> {
        self.rules.get(index).cloned()
    }

    /// Obtains a rule with all variables expanded in the recipe
    /// according to the current variable context.
    ///
    /// Pattern-rules (i.e `%.o: %.c`) are expanded to match
    /// the name if required (for instance if called with `foo.o`, `%.o` will be considered
    /// to be matching).
    ///
    /// If a "magic" rule exists for the requested kind of file,
    /// it will be the default value.
    pub fn get_rule(&self, name: &str) -> Option<Rule> {
        self.get_rule_index(name).map(|index| {
            let mut r = self.rules[index].clone();
            r.commands.iter_mut().for_each(|mut c| self.vars.expand_line(false, &mut c));
            r
        })
        .or_else(|| { // Try to find a pattern rule that matches
            self.rules.iter()
                .find_map(|r| {
                    let mut pattern = r.name.split('%');
                    let (prefix, suffix) = match (pattern.next(), pattern.next()) {
                        (Some(p), Some(s)) => (p, s),
                        _ => return None, // not a pattern rule
                    };
                    if name.starts_with(prefix) && name.ends_with(suffix) {
                        let stem = name.strip_prefix(prefix).unwrap_or(name);
                        let stem = stem.strip_suffix(suffix).unwrap_or(stem);

                        Some(Rule {
                            name: name.to_owned(),
                            deps: r.deps.iter().map(|d| match d {
                            RuleRef::Unresolved(n) => {
                                let new_name = n.replace('%', stem);
                                self.get_rule_index(&new_name).map(RuleRef::Resolved).unwrap_or(RuleRef::Unresolved(new_name))
                            },
                            x => x.clone(),
                        }).collect::<Vec<_>>(),
                            commands: r.commands.clone(),
                        })
                    } else {
                        None
                    }
                })
        })
        .or_else(|| {
            // Default to a built-in rule
            //
            // TODO: there are more than these, see https://www.gnu.org/software/make/manual/html_node/Catalogue-of-Rules.html
            if name.ends_with(".o") {
                let c_name = name.replace(".o", ".c");
                Some(Rule {
                    name: name.to_owned(),
                    deps: vec![
                        self.get_rule_index(&c_name).map(RuleRef::Resolved).unwrap_or(RuleRef::Unresolved(c_name.clone()))
                    ],
                    commands: vec![
                        {
                            let mut cmd = format!("$(CC) $(CPPFLAGS) $(CFLAGS) -c {}", c_name);
                            self.vars.expand_line(false, &mut cmd);
                            cmd
                        }
                    ]
                })
            } else if !name.contains('.') {
                let o_name = name.to_owned() + ".o";
                Some(Rule {
                    name: name.to_owned(),
                    deps: vec![
                        self.get_rule_index(&o_name).map(RuleRef::Resolved).unwrap_or(RuleRef::Unresolved(o_name.clone()))
                    ],
                    commands: vec![
                        {
                            let mut cmd = format!("$(CC) $(LDFLAGS) {} $(LOADLIBES) $(LDLIBS)", o_name);
                            self.vars.expand_line(false, &mut cmd);
                            cmd
                        }
                    ]
                })
                
            } else {
                None
            }
        })
        .map(|r| Rule {
            commands: r.commands.iter().map(|c| {
                let ref_to_string = |rule_ref: &RuleRef| match rule_ref {
                    RuleRef::Unresolved(n) => n.clone(),
                    RuleRef::Resolved(idx) => self.get_rule_at(*idx).map(|x| x.name).unwrap_or_default(),
                };
                c.replace("$@", name)
                    .replace("$<", &r.deps.get(0).map(ref_to_string).unwrap_or_default())
                    .replace("$^", &r.deps.iter().map(ref_to_string).collect::<Vec<_>>().join(" "))
            }).collect(),
            ..r
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_logical_lines() {
        let text = r#"Hello\
world
yay
test\
    abcd"#;
        let mut ll = logical_lines_of(text);
        assert_eq!(ll.next(), Some("Hello world".into()));
        assert_eq!(ll.next(), Some("yay".into()));
        assert_eq!(ll.next(), Some("test abcd".into()));
        assert_eq!(ll.next(), None);
    }

    #[test]
    fn cmd_outside_of_rule() {
        assert_eq!(Error::CommandOutsideOfRule, Makefile::try_parse("\techo oh no").unwrap_err())
    }

    #[test]
    fn rule() {
        let mf = Makefile::try_parse("hello: world ; foo\n\tbar\n\nbaz:").unwrap();
        assert_eq!(&mf.rules[0].name, "hello");
        assert_eq!(mf.rules[0].deps, vec![ RuleRef::Unresolved("world".to_owned()) ]);
        assert_eq!(mf.rules[0].commands, vec![ "foo".to_owned(), "bar".to_owned() ]);
        assert_eq!(&mf.rules[1].name, "baz");
    }

    #[test]
    fn variable_rule_name() {
        let mf = Makefile::try_parse("RULE=hello\n\n$(RULE):\n\techo yay").unwrap();
        assert_eq!(&mf.rules[0].name, "hello");
    }

    #[test]
    fn get_rule() {
        let mf = Makefile::try_parse("CC=clang\nCFLAGS=-Wall -g\n\nlib.o: lib.c\n\t$(CC) $(CFLAGS) -c lib.c").unwrap();
        let rule = mf.get_rule("lib.o").unwrap();
        assert_eq!(&rule.name, "lib.o");
        assert_eq!(rule.deps, vec![ RuleRef::Unresolved("lib.c".into()) ]);
        assert_eq!(&rule.commands[0], "clang -Wall -g -c lib.c");
    }

    #[test]
    fn pattern_rule() {
        let mf = Makefile::try_parse("%o: %c\n\techo compiling...").unwrap();
        let rule = mf.get_rule("foo.o").unwrap();
        assert_eq!(&rule.name, "foo.o");
        assert_eq!(rule.deps, vec![ RuleRef::Unresolved("foo.c".into()) ]);
    }

    #[test]
    fn deps_resolution() {
        let mf = Makefile::try_parse("all: app\nmain.o: main.c\nlib.o: lib.c\napp: main.o lib.o").unwrap();
        let all = mf.get_rule("all").unwrap();
        let app_index = match all.deps[0] {
            RuleRef::Resolved(x) => x,
            _ => panic!("Unresolved rule should be resolved")
        };
        let app = mf.get_rule_at(app_index).unwrap();
        let main_o_index = match app.deps[0] {
            RuleRef::Resolved(x) => x,
            _ => panic!("Unresolved rule should be resolved")
        };
        let lib_o_index = match app.deps[1] {
            RuleRef::Resolved(x) => x,
            _ => panic!("Unresolved rule should be resolved")
        };
        let main_o = mf.get_rule_at(main_o_index).unwrap();
        let lib_o = mf.get_rule_at(lib_o_index).unwrap();
        assert_eq!(main_o.deps[0], RuleRef::Unresolved("main.c".into()));
        assert_eq!(lib_o.deps[0], RuleRef::Unresolved("lib.c".into()));
    }

    #[test]
    fn stable_deps() {
        let mf = Makefile::try_parse("all: app\napp: app.o\napp.o: app.c").unwrap();
        let mut mf2 = mf.clone();
        mf2.resolve_deps();
        assert_eq!(mf, mf2);
    }

    #[test]
    fn automatic_variables() {
        let mf = Makefile::try_parse("%.o: %.c foo\n\techo $@ $<\n\techo $^").unwrap();
        let rule = mf.get_rule("hello.o").unwrap();
        assert_eq!(&rule.commands[0], "echo hello.o hello.c");
        assert_eq!(&rule.commands[1], "echo hello.c foo");
    }

    #[test]
    fn built_in_exe() {
        let mf = Makefile::try_parse("CC=clang").unwrap();
        let rule = mf.get_rule("app").unwrap();
        assert_eq!(&rule.name, "app");
        assert_eq!(rule.deps, vec![ RuleRef::Unresolved("app.o".into()) ]);
        assert_eq!(&rule.commands[0], "clang  app.o");
    }

    #[test]
    fn built_in_object() {
        let mf = Makefile::try_parse("CC=clang").unwrap();
        let rule = mf.get_rule("foo.o").unwrap();
        assert_eq!(&rule.name, "foo.o");
        assert_eq!(rule.deps, vec![ RuleRef::Unresolved("foo.c".into()) ]);
        assert_eq!(&rule.commands[0], "clang   -c foo.c");
    }
}
