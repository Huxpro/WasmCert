Dev Notes
=================================

Gotcha
------

### Oct 2018 Rename

A full renaming is happened: <https://github.com/WebAssembly/spec/issues/884#issuecomment-426433329>
Basically, More uniformed `namespace.action_param_param2` less weird symbol. I think it's good

```wast
;; table declaration
anyfunc -> funcref

;; core instructions
get_local -> local.get
set_local -> local.set
tee_local -> local.tee
get_global -> global.get
set_global -> global.set

;; between numeral
i32.wrap/i64 -> i32.wrap_i64
i32.trunc_s/f32 -> i32.trunc_f32_s
...

```

### Different format

Both works...

```wast
;; func-like = syntax sugar?
(func $add (param $lhs i32) (param $rhs i32) (result i32)
    (i32.sub (get_local $lhs) (get_local $rhs)))


;; stack
(module
  (func $add (param $lhs i32) (param $rhs i32) (result i32)
    get_local $lhs
    get_local $rhs
    i32.add)
  (export "add" (func $add))
)
```




[Understanding WebAssembly text format
](https://developer.mozilla.org/en-US/docs/WebAssembly/Understanding_the_text_format)
-------------------------------------

- Stack memory
  - `param i32`
  - `local $name f64`
  - `get_local 0` / `get_local $name`
    - when called with index, the indexed starts from parameter
    - `param` is just assembler-time mnemonics 

- Stack Machine
  - `get_local` push
  - `set_local` pop
  - `i32.add`   pop 2

- Text format (wast: _W_eb _AS_sembly _T_ext)
  - S-expression (officially?)
    - comment line  `;; ...` 
    - comment block `(; ... ;)` 

- Types
  - `i32` `i64` `f32` `f64`
  - `[t1*] -> [t2?]` 表示一段代码的 pop 和 push (<=1 in current ver)

- Func
  - `(func $add ...)`
  - `(export "add" (func $add))`


- Module


### `add` example

```wast
(module
  (func $add (param $lhs i32) (param $rhs i32) (result i32)
    get_local $lhs
    get_local $rhs
    i32.add)
  (export "add" (func $add))   
)
```


### exporting to JS / shorthand `export`

```wast
(module
  (func $getAnswer (result i32)
    i32.const 42)
  (func (export "getAnswerPlus1") (result i32)  ;; declared export
    call $getAnswer  ;; call function at same module!
    i32.const 1
    i32.add))
```
```js
WebAssembly.instantiateStreaming(fetch('call.wasm'))
 .then(obj => {
    console.log(obj.instance.exports.getAnswerPlus1());  // "43"
  });
```


### importing from JS

```wast
(module
  (import "console" "log" (func $log (param i32)))
  (func (export "logIt")
    i32.const 13  ;; parameter pushed to stack
    call $log))
```
```js
var importObject = {
  console: {
    log: function(arg) {
      console.log(arg);   }}};

WebAssembly.instantiateStreaming(fetch('logger.wasm'), importObject)
  .then(obj => {
    obj.instance.exports.logIt();
  });
```


### globals 

> global, accessible from both JS and across `WAsm.Module` instances
> this allows _dynamic linking_ of multiple modules

```wast
(module
   (global $g (import "js" "global") (mut i32))
   (func (export "getGlobal") (result i32)
        (get_global $g))
   (func (export "incGlobal")
        (set_global $g
            (i32.add (get_global $g) (i32.const 1))))
)
```
```js
const global = new WebAssembly.Global({value: "i32", mutable: true}, 0);
```


### Wasm Memory

> WebAssembly provides _memory_. 
> memory is just a _large array of bytes_ that can grow over time. 

- `i32.load`  reading and
- `i32.store` writing from linear memory






[Spec](https://webassembly.github.io/spec)
==========================================

Notation
--------

Terminal is written in _sans-serif_. => constructor (~= textual)
Non-Terminal is written in _italic_ _serif_. => you need to give a constructor name...

Execution/Runtime Structure
---------------------------

### Values

### Results

```bnf
retuls ::= val*     -- at most one value at current version 单值返回
         | trap
```

### Stores 

> allocated instances of _functions, tables, memories, globals_ of runtime.

Heap? 
- 18 CPP 只称 linear memory 这部分为 Heap, 
- 17 PLDI 没有用这个词...
- 14 JSCert 中区分 Object Heap 与 Environment Record Heap, 统称为 state

```hs
-- record
store ::= { funcs    funcinst*,      -- 注意这里是"inst"ance，不是 "instr"uction
            tables   tableinst*,
            mems     meminst*,       -- Isabelle [meminst] 
            globals  globalinst* }
```

### Addresses

> for referencing instances of _functions, tables, memories, globals_

```hs
addr ::= Nat
blahaddr ::= addr  -- blah 指代上述几种堆对象
```

### Module Instances

类型与地址……作用更类似 environment，提供 scope 的作用

```hs
moduleinst ::= { types        functype* 
                 funcaddrs    funcaddr*,
                 tableaddrs   tableaddr*,
                 memaddrs     memaddr*,
                 globaladdrs  globaladdr*,
                 exports      exportinst* }
```


### Administrative Instructions  行政指令……

> only relevant for _formal notation_
> 这些应该不在 text format 可以敲出来的范围内，比如没有一个 `(trap)`

为了 express reduction 关系中的 trap（困境）, calls（因为闭包？）, control instruction（显式 label?），需要拓展 instr 的语法：

```hs
instr ::= ...
        | trap             -- ocurrence of a trap (so it can be bubbled up, ultimately reducing to single trap, signalling abrupt)
        | invoke funcaddr  -- call closure 
        | init_elem ...
        | init_data ...
        | label_n {instr*} instr* end
        | frame_n {frame}  instr* end   -- 在 PLDI 17 里没有 frame 概念，用得是 local_n {i; v*} e* end  -- i 是 store 的索引, v 是 local
```

#### Block Contexts

同样，需要 explicitly count `k` of labels surrounding the hole

```hs
B^0   ::= val* [_] instr*
B^k+1 ::= val* label_n{instr*} B^k end instr*
               -----------------------
                   inner block B^k
```

这样就可以定义

     label_0{instr∗} B^l [br l] 𝖾𝗇𝖽  ↪  instr∗




WASM 17 PLDI
============





Thoughts
========

Discussion
----------

* What are some of the defining features of Wasm?
  How could they interact with the formal verification?

* Specifically, what's the problem and solution of mechanically formalizing "structural control flow"?

* Besides the type safety, the original paper (PLDI 17) paper also state that soundness proof also brings other safety and security properties:
  - memory safety
  - statically structure of operand stack
  - inaccessibility of code addresses / call stack
  - encapsulation / abstraction on the module and function boundary
  How did they get proved?

* The paper made underlying representation of WebAssembly types, the heap, and the host environment abstract via parameterised polymorphism.
  Do you like this idea?

* How concerned are you about the notion of "eyeball closeness"?
  Especially when the current spec have been different with the representation in the original paper and this verification paper?

* How much do you concern about the non-deterministic part of Wasm?

* What could be possibly improved if the project was using Coq?
  - leveraging Coq's little meta-programming?
  - Potential interact with JSCert (easier)?
  - larger community?
  - better extraction? (Ocaml/Haskell)
  - prove in dependently-typed vs. HOL (Idk really get the difference...)
    > https://stackoverflow.com/questions/30152139/what-are-the-strengths-and-weaknesses-of-the-isabelle-proof-assistant-compared-t
    - this could help with eliminating (some), minimizing "administrative instructions"?
    - missing the law of the excluded middle (might be okay since PL is very constructive...?)

* How annoyed do you think the paper and the spec are somewhat different and the paper still state the "eyeball-closeness";

* Any potential application if we have both verified Wasm and verified JavaScript (e.g. JSCert)?



WASM
----

> neither just for the Web, nor just Assembly

What are some of the defining features of WASM (that possibily affect formalization)? 

- stack machine
  - static?
  
- linear memory
  - raw byte arrays

- some relatively high-level abstraction ...
  - module / sandboxes 
  - no arbitrary jump / only structured control flow
    - no irreducible control flow / fast verification
    - producers relooper algo (irreducible -> reducible)

- future...even even more higher-level
  - exceptions / GC

- type checking
  - type-safe / memory safe
  - soundness proof!

- formal semantics!
  - operational semantics / reduction rules
    - deterministic (up to NaN bit patterns)
    - no undefined 
  - type system / typing rules
    - embarrassingly simple
    - ensuring stack layout is entirely static
    - machine-verified in Isabelle

- reference interpreter in OCaml

- JavaScript as FFI
  - access by JS via `ArrayBuffer`
  - and `SharedArrayBuffer` for multi-threading WASM




Course Notes
------------

- Memory-safety
  - read garbage as int....fine if not used as closure (which might not be valid instructions)
  - + dynamically check (bound check / function pointer / ) 

- Parametricity
  - abstract `type` in `module`
