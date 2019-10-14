Engineering Notes
=================

> most _issue_ would be noted via comment.
> where here we note things we approved implicitly.


Naming Convention
-----------------

Currently, we follow the spec naming using all lower case.

But we could follow the reference interpreter to use `CamelCase` for constructor.
This could increase some readbility in code and resolve some name conflicts.



Eyeball Closeness Convention
----------------------------

"eyeball closeness" is not easy to achieve.
There are many notational overloading from real, industrial specification of Wasm.
The real spec is trickier to formalize than the paper one, which is made to be cleaner.

The coq formalization need to:
- explicity distinguish between relation on a single instr vs. on a instruction sequences.
  * e.g. `instr` vs. `instr*`

- explicity distinguish between implicit-"definitional equivalence"
  * e.g. `expr = instr*`.

- choosing the generality between the most general (original paper formalization) and real-world constraints (from the real-world spec).
  * e.g. `resulttype`
    - `list` vs. `option`

- explicity option type: `Some` and `None` are treat as subsumption rather than disjointed. `resulttype` could implicitly be a `Some resulttype`. and `[]` could be either `None` or `nil`


On the use of `resultype`
-------------------------

### Issues

[spec / should functions return a resulttype?](https://github.com/WebAssembly/spec/issues/559)
[spec / on the use of result type](https://github.com/WebAssembly/spec/issues/1071)


### Rationales

#### 1. the abstract syntax is defined to be in 1-to-1 correspondence with the binary representation

that's why `block` and `loop` can only take one "variant-length "


### Solution

We are moving to [multi-value](https://github.com/WebAssembly/multi-value) proposal.
[a better foundation for a mechanization?](https://github.com/WebAssembly/multi-value/issues/23)

> Yes, basing it on the multi-value proposal might be preferable.  -- @rossberg




Structure.v
-----------



Validation.v
------------




Execution.v
-----------
