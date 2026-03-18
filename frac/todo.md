# TODO

- fix up rational handling
- Anything marked with TODO in code
- probably a ton of uniqueness checks
- handle products of variables

# Done
- add cases to type ast for new types
- add cases to parser for new types
- rename old type to protocol, bc type now includes permission + id
- adjust lolli and tensor to take full channel types
- add cases to statement ast for sending and recieving permissions and ids
- change channel type in statements to just be the name, no mode or dollar sign
- remove unused cases from parser
- remove unused cases from ast
- check for id freshness on spawning
- check that you only use known ids/perms when spawning/tail-calling
- forbid * from being the value we send over a forall/exists for permissions? otherwise it's invalid to split a channel at a variable permission
- Better permission equality
- Better permission parsing
- use rationals instead of floats for permissions
- share+own now allowed inside immutable operations again (just revert the commit)
- continue only has to name unlocked channels
- new items in continuation
- substitute out p_c in \\\\//R
- changes to start (new syntax + has to match)
- changes to /\\R rule (new syntax for immut blocks, new variable in V, multiply unlocked context + continuation context by this amount, acts like a forall (also change /\\L))
- don't multiply in tensor and lolli
