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

- check that you never send a down arrow (including double down) or use it as a parameter to a process definition (makes it so they can't be applied eagerly)
- right side doesn't get reconstructed
  - we can in theory eagerly create mut blocks, but I think that will feel weird
  - we cannot eagerly create immut blocks without significant futher inference for the channel list
  - we can't really reconstruct the existence of continue, and inferring the channels to write is tricky
- that leaves left side reconstruction
  - finish and mutate should be inserted eagerly, this amounts to checking at each type-check step if either rule applies to anything in the context and applying them
  - start should be inserted lazily, this is more complicated. essentially for any attempt at communication on the left, if the type is an up arrow than we want to do a start then recheck the type
- infer necessary id when *sending* to ?a. <A, p, a> pattern and dual
- infer necessary id when *receiving* from ?a. <A, p, a> pattern and dual
  - give id a fresh identifier that I suppose then never gets exposed externally
- infer necessary id for *newly spawned* channel 
  - again give it a fresh identifier that can't be explicitly mentioned
  - requires changing the parser
- infer necessary id for *arguments* to a spawned channel
  - requires assumption that the id parameters are exactly the ids of the channel arguments
- infer permissions in similar settings?
  - probably not, it doesn't come up as much and is generally more complicated
