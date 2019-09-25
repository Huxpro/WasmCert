Code Style
==========

> pretty much Software Foundation convention.

[Build](https://coq.inria.fr/refman/practical-tools/utilities.html#building-a-coq-project-with-coq-makefile)
------------------------------------------------------------------------------------------------------------

> The main piece of metadata needed in order to build the project are the command line options to `coqc`
> [coqc CLI options](https://coq.inria.fr/refman/practical-tools/coq-commands.html#command-line-options)

Use `_CoqProject` file:

```
-Q . LF
```

> The `coq_makefile `utility can be used to set up a build infrastructure for the Coq project based on makefiles.

```sh
coq_makefile -f _CoqProject -o Makefile
make
```

manual `coqc`

```sh
coqc <blah>.v -Q . Wasm
```




[Coq Style](https://github.com/coq/coq/wiki/CoqStyle)
-----------------------------------------------------

### Headers

```coq
(************************************************************************)
(* Copyright <YEAR> <AUTHOR>                                            *)
(* <LICENSE>                                                            *)
(************************************************************************)
```

[Documenting w/ `coqdoc`](https://coq.inria.fr/refman/practical-tools/utilities.html#documenting-coq-files-with-coqdoc)
-----------------------------------------------------------------------------------------------------------------------

### Basic

Special comment, Code, *PrettyPrinting*, Escaping LaTex/HTML

```coq
(** text *)
(** coq code: [fun x => u] *)
(** printing  *token* %...LATEX...% #...html...# *)
(** printing  *token* $...LATEX math...$ #...html...# *)
 ```

### Section

Followed with 1-4 `*` (`h1` to `h4`)

```coq
(** * Well-founded relations

    In this section, we introduce...  *)
```

### List

Leading dash

```coq
(**
    We go by induction on [n]:
    - If [n] is 0...
    - If [n] is [S n'] we require...

      two paragraphs of reasoning, and two subcases:

      - In the first case...
      - In the second case...

    So the theorem holds.
*)
```

### Horizontal Lines

4 dashes `----`


### Emphasis

_underscore_
