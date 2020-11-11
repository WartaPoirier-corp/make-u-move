# Make U Move

A Makefile parser.

- [x] Recursive variables (`VAR=val`)
- [x] Rules, with dependencies and recipes
- [ ] Patterns (`%` in rules and dependencies)
- [ ] Other kinds of variables
- [ ] Multiline variables
- [ ] A lot of built-ins
- [ ] Probably a lot of other things I forgot about

## Example

```rust
use make_u_move::{Makefile, RuleRef};

let mf = Makefile::try_parse(include_str!("Makefile")).unwrap();
let all_rule = mf.get_rule("all").unwrap();

println!("This name is named {}", all_rule.name);

let main_rule_index = match all_rule.deps[0] {
    RuleRef::Resolved(idx) => idx,
    RuleRef::Unresolved(name) => unreachable!(),
};
let main_rule = mf.get_rule_at(main_rule_index).unwrap();
// Print the command with variables expanded
println!("The first dependency of 'all' is built with : {}", main_rule[0]);
// Outputs this command : clang main.o lib.o -o main
```

Explores the following Makefile:

```make
CC=clang

all: main

%.o: %.c
    $(CC) -c $< -o $@

main: main.o lib.o
    $(CC) $^ -o $@
```
