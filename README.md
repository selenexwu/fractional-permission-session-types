# FracST
## Fractional Permission Session Types
This repository contains an implementation of the FracST typechecker and program reconstruction algorithm.

## Installation

### Prerequisites

#### Opam
The instructions for installing opam are available on the [opam installation page](https://opam.ocaml.org/doc/Install.html). Please install the latest version of opam.

##### Configuring Opam
To configure opam for the first time and install a specific version of OCaml, please run the following (skip if you have already configured opam)
```
$ opam init
```

### Installing Dependencies
Clone the repository.
```
$ git clone https://github.com/selenexwsu/FracST.git
$ cd FracST
```

Now, we create a local opam switch to contain the necessary dependencies. This will also build FracST.
```
$ opam update
$ opam switch create . 5.5.1 -y
```

Afterwards, we can make sure `dune` is available at the command-line using
``` 
$ eval $(opam env)
```

### Building
To rebuild, simply run the make command at the top-level.
```
$ make
```

### Troubleshooting
1. Sometimes, your `$ make` command may fail with the error "dune: command not found". In this case, try restarting your terminal and running `$ make` again. Or you may need to run `$ eval $(opam env)` in your terminal again unless this command is already in your `.bashrc`.

2. Sometimes, the core library of ocaml is not correctly installed (generally, if you already have an old installation of core). In these cases, simply run `$ opam install core` and try running `$ make` again.

3. Sometimes, `$ opam upgrade` can fail with the following error particularly on Linux machines.
```
The packages you requested declare the following system dependencies. Please
make sure they are installed before retrying:
    m4
```
Please make sure you install `m4`. On Ubuntu machines, this simply amounts to running the command `$ sudo apt install m4`.

### Testing
To tests whether your installation works, run the following command to typecheck a basic example:
``` 
$ ./_build/default/bin/fracst.exe -v 2 -s implicit tests/implicit/nat.frac
```

If everything is working correctly, you should see the typechecking time printed to the console.

### Executing
The make command creates an executable for FracST at `_build/default/bin/fracst.exe`.
To typecheck a file with FracST, run
```
$ ./_build/default/bin/fracst.exe <file-path>
```

By default the program reconstruction algorithm doesn't run. In order to tell FracST to use program reconstruction, pass the `-s implicit` flag. 

A collection of examples is provided in the `tests` directory, both in `explicit` and `implicit` forms.

For example, the following commands typecheck the natural number example without and with program reconstruction respectively:
```
$ ./_build/default/bin/fracst.exe ./tests/explicit/nat.frac
$ ./_build/default/bin/fracst.exe -s implicit ./tests/implicit/nat.frac
```

The `-v` flag controls verbosity and defaults to `1`. If set to `2`, the typechecker will print the typechecking time, and a trace of failed typechecks.

To see this, you can run the following command to typecheck a deliberately incorrect implementation of `nat`
```
$ ./_build/default/bin/fracst.exe -s implicit ./tests/implicit/nat_wrong.frac
```

## Writing FracST programs
Writing session-typed programs needs some guidance. First, I will introduce the basic declarations. There are three forms of declarations:

#### Type Definitions
New type names can be defined using the following syntax `type v = A` where type name `v` has definition `A`. As an example, the `queue` type is defined as follows:
```
type queue = /\k. &{ins : \\// !a. <A,*,a> -o queue,
                    del : \\// +{none : 1,
                                 some : ?a. <A,*,a> * queue},
                    len : ?a. <nat,*,a> * \/ queue}
```
Here, `/\`, `\/`, and `\\//` are used to denote the up, down, and double down arrows, `!a` and `?a` are used to receive and send identifiers respectively, `-o` and `*` are used to receive and send channels, `+` and `&` denote internal and external choice, and `1` indicates termination.

Formally, the grammar for session types is as follows:
```
<A> ::= +{l1 : <A1>, ..., ln : <An>}       // internal choice
      | &{l1 : <A1>, ..., ln : <An>}       // external choice
      | <<A>,<p>,a> * <A>                  // tensor
      | <<A>,<p>,a> -o <A>                 // lolli
      | 1                                  // one
      | /\ <A>                             // up (start immutable session)
      | \/ <A>                             // down (end immutable session)
      | \\// <A>                           // double down (mutate)
      | !a. <A>                            // forall identifier
      | ?a. <A>                            // exists identifier
      | !!p. <A>                           // forall permission 
      | ??p. <A>                           // exists permission
      | <id>                               // type name (e.g. auction)
      | ( <A> )
    
<p> ::= *                // owned permission 
      | <int>/<int>      // fractional permission
      | <id>             // variable permission
      | <int>/<int>*<id> // fraction of variable permission
      | <p> + <p>        // sum of permissions
```

#### Process Definitions
New processes are defined using the syntax `proc f[ids]{ps} : (c1 : <A1,p1,a1>), ... (cm : <Am,pm,am>) |- (c : A) = P` where the process name is `f`, its declared identifier variables are `ids`, its declared permission variables are `ps`, its context is a sequence of channel arguments `ci` of type `<Ai,pi,ai>`, and the offered channel is `x` of type `A`. The definition is denoted by the expression `P`. An empty context is described using `.`.

Formally, the context is denoted with
```
<context> ::= .     // empty context
            | <ctx> // non-empty context

<ctx> ::= (x : <<A>,<p>,a>), <ctx>
```

### Process Syntax
Formally, the syntax for processes is below.
```
<ch-list> ::= <id> | <id> <ch-list> // channel list

<P> ::= {a}, <ch> <- f[ids]{ps} <- <ch-list> ; <P>   // spawn process f
      | {a}, <ch> <- f[ids]{ps} <- <ch-list>         // tail call f
      | <ch> <-> <ch>                                // forwarding
      | send <ch1> <ch2> ; <P>                       // send <ch2> on <ch1>
      | <ch2> <- recv <ch1> ; <P>                    // receive <ch2> on <ch1>
      | <ch>.k ; <P>                                 // send label k on <ch>
      | case <ch> ( <branches> )                     // case analyze on label received on <ch>
      | close <ch>                                   // close channel <ch>
      | wait <ch> ; <P>                              // wait for <ch> to close
      | immut <ch-list> { p => <P> }                 // immutable block using <ch-list>
      | continue <ch-list>                           // tail call immutable session with <ch-list>
      | mut { <P> }                                  // abort immutable session
      | start <ch>{<p>} ; <P>                        // start immutable session on <ch> with permission <p>
      | finish <ch> ; <P>                            // finish immutable session on <ch>
      | mutate <ch> ; <P>                            // abort immutabl session on <ch>
      | <ch1>, <ch2> <- split <ch> ; <P>             // split <ch> into <ch1> and <ch2>
      | <ch> <- merge <ch1>, <ch2> ; <P>             // merge <ch1> and <ch2> into <ch>
      | share <ch> ; <P>                             // share <ch>
      | own <ch> ; <P>                               // own <ch>
      | send {a} <ch> ; <P>                          // send identifier a on <ch>
      | {a} <- recv <ch> ; <P>                       // recieve identifier a on <ch>
      | send {{p}} <ch> ; <P>                        // send permission p on <ch>
      | {{p}} <- recv <ch> ; <P>                     // recieve permission p on <ch>
```
