Engineering Notes
=================

> most _issue_ would be noted via comment.
> where here we note things we approved implicitly.


Naming Convention
-----------------

Currently, we follow the spec naming using all lower case.

But we could follow the reference interpreter to use `CamelCase` for constructor.
This could increase some readbility in code and resolve some name conflicts.


Distinguish ValType and FuncType
--------------------------------------------------------

Originally, I used `vt` for `valtype` and `ft` for `functype`.
Later on I found that's the only two type and `t` could represent `valtype` without any ambigiouty.



Distinguish Wasm Value and Concrete Value/Constant Representation
-----------------------------------------------------------------

- Wasm `val` IS `instr`

### Planned Solution.

- `val` always mean Coerced `val >-> instr`  i.e. `val = Const v`
- `v` always mean polymorphic (and type-dependent) value, i.e. `v = i32 c`
  - alternative name `tc` (typed const)
  - alternative name `pv` (polymorphic value)
  - alternative name `cv` (concrete value)
- `c` or `i` (when used as index) always mean const (w/o type) `c`

- `op I32.t I64.t F32.t F64.t.` should be seen as a convenience for establish type-dependent value in the meta-language 
  - it could be named as `value` or `typed_const` to distinguish with above `val`
  - it could still be name as `val` 
    * they are Equal up to one `Coercion`
    * so we can still write `list val`. (and we assume the use of above `val` is a local shadowing)


### Naming Convention

Currently, When named inside inductive relation, we follow the Wasm spec:
- `v` or `val` = instr `Const c : instr`
- `c`          = concrete const representation


But, the concrete const `c` is currently represented as

```coq
Definition val := op I32.t I64.t F32.t F64.t.
```

(Yup it's confusing...) We might change the `val` name here later....

#### Type

Since the `c` (or this inductive `val` definition) is a inductive def.
We simply use defined `type_of c` to projection-then-map to `valtype`

#### Problem

这里**最重要的问题**在于：使用 `instr` 并不足以从类型上区分出「这是一个 `value`」。
所以使用 `Definition val` 的好处是可以区分开来并且可以 `Coercion Const` 过去 
但是这样的话命名就很尴尬了

所以我们有 

- `Const: val -> instr`
- `⇈: val -> admin_instr`

但是这样命名就比较诡异了


### Coercion `<->` Proof-Carry

#### 如果默认采用 val 然后 Coercion

- `-> val`

自己就是，可以和 `I32.zero` 比较

- `-> instr`

`Coercion Const: val >-> instr` 

这个的问题在于，
1. cast 过去信息可能会丢掉
2. `Coercion` 经常不 work，不然如果全程都能把 `val` Coerce 成 instr 用那么完美


#### 如果默认采用 Proof-Carry 的 dependent pair

```coq
Inductive value := 
  | Value (i : instr) (E : ⊢v i ∈ t).

(* or *)
Record value := {i: instr ; E : ⊢v i ∈ t }.
```

- `value -> instr`

```coq
value.(i)
```

- `value -> val`  How ??? (在于 `I32.zero` cmp 时需要)

```coq
match value.(H) with
| Value c => c       (* error *)
end.
```

We can't eliminate proof `H` to get back a concrete `c`?
本来以为好像 proof-carry value 要更好但是在如何获得 c 这件事上失败了



Eyeball Closeness Convention
----------------------------

"eyeball closeness" is not easy to achieve.
There are many notational overloading from real, industrial specification of Wasm.
The real spec is trickier to formalize than the paper one, which is made to be cleaner.

The coq formalization need to:
- explicity distinguish between relation on a single instr vs. on a instruction sequences.
  * e.g. `instr` vs. `instr*`
  * 用 mutually recursive 解决

- explicity distinguish between implicit-"definitional equivalence"
  * e.g. `expr = instr*`.
  * 这个仍然需要 investigation

- choosing the generality between the most general (original paper formalization) and real-world constraints (from the real-world spec).
  * e.g. `resulttype`
    - `list` vs. `option`
  * 用移动到 multi-value 以及 coercion 解决

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
