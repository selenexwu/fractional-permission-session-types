# TODO

- Anything marked with TODO in code
- Better permission parsing
- check that you only use known ids/perms when spawning/tail-calling
- check for id freshness on spawning
- use rationals instead of floats for permissions
- probably a ton of uniqueness checks

# Done
- add cases to type ast for new types
- add cases to parser for new types
- rename old type to protocol, bc type now includes permission + id
- adjust lolli and tensor to take full channel types
- add cases to statement ast for sending and recieving permissions and ids
- change channel type in statements to just be the name, no mode or dollar sign
- remove unused cases from parser
- remove unused cases from ast
