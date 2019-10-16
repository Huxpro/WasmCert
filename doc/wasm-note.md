Notes on WebAssembly
=================================

Gotcha - Oct 2018 Rename
------------------------

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


Gotcha - Assembler Name (Text Format)
------------------------------------

As MIPS where we use `$r0` to alias first register,
Wasm allow `$`-prefixed alias name. 

```wast
(func (param i32) (param f32) (local f64)  ;; unnamed
  local.get 0
  local.get 1
  local.get 2)

;; for convenience
(func (param $p0 i32) (param $p1 f32) (local $x0 f64)  ;; aliased
  local.get $p0
  local.get $p1
  local.get $x0)
```
Assembler will compute those assembler-time mnemonics into integer index: `$p0 -> 0` `$x0 -> 2`.


Gotcha - Folded Form (Text Format)
----------------------------------

> <https://webassembly.github.io/spec/core/text/instructions.html#folded-instructions>

```wast
(local.get $x) (local.const 2) i32.add

;; folded into
(i32.add (local.get $x) (local.const 2))
```

```wast
(func $add (param $lhs i32) (param $rhs i32) (result i32)
  get_local $lhs
  get_local $rhs
  i32.add)

;; folded into
(func $add (param $lhs i32) (param $rhs i32) (result i32)
    (i32.add (get_local $lhs) (get_local $rhs)))
```


Gotcha - Typecheck Structural (`block`, `if`, `loop`) by labels
------------------------------------------------------------------

1. `block`, `if`, `loop` prepend label to the current `C`ontext and **labels are typed**
   * prepend meaning they are the closest one to jump out and would indexed 0

2. `br i` will jump to the `end` of the `i`-indexed block and continue from there
   * how do we know the type after jump? 
   * by fetching the `label`! **labels are typed**
   * **Execution will take only as many valtypes as labels said and unwind anything else**


Gotcha - `br`, `unreachable` - Stack Polymorphic
------------------------------------------------------------------

> PLDI 17 paper 4.1 typing rules - validation also talked about this.

_value polymorphic_ is trivial.  but _stack polymorphic_ is very interesting...

```wast
(func $stkpoly (param) (result i32)
  i32.const 1
  block (result i32)
    i32.const 10
    i32.const 100
    br 0
    i32.add
  end
  i32.add
```

我们看一下 `br` 的 typing rule

$$
            C.labels[l] = [t^\ast]
    ------------------------------------------
    C ⊢ br l : [t_1^\ast t^\ast] -> [t_2^\ast]
$$

与 execution:

$$  label_n {instr^\ast} B^l [val^n (br l)] end  ↪   val^n instr^\ast  $$


### 0. `block` 的静态类型信息在哪？

`block` 给的唯一 type 信息就是注册在 `C.labels` 里的 `label`，
`label` 只告诉我们 `(result i32)`，所以 `$stkpoly` 的 validation 是

$$
   i32.const : i32        block : i32
  ------------------------------------
      i32.add : [i32 i32] -> [i32]
    --------------------------------
         $stkpoly : [] -> [i32]
$$


### 1. 但是如果是 unconditional jump，如何保证之后的 type safety?

可以看到，`block` 内部其实压了两个 `i32` 如果只是 trivial 的 unconditional jump 的话，
栈上就是 `(i32 i32 i32)(i32.add) ↪  i32 i32` 这里和 `$stkpoly (result i32)` 直接就 unsafe 了。

所以 `br` 做的事情是拿到 `label` 的 arity `n`，然后只留下栈上 `n` 个 `valtype`，其他都 unwinding 掉


### 2. Incompleteness

`unreachable` code is still required to typed.

```wast
block (result i32)
  i32.const 2
  i32.const 1
  br 0
  i64.add ;; deadcode
end
```

https://github.com/WebAssembly/spec/issues/1078

> Allowing but not type-checking unreachable code would break **decomposability** and requires the spec to provide a syntactic definition of reachability
> https://github.com/WebAssembly/design/blob/master/Rationale.md#why-polymorphic-stack-typing-after-control-transfer
> http://webassembly.github.io/spec/core/appendix/algorithm.html



Wasm - Misc
-----------

> `Wasm-` prefixed sections are thoughts after reading this tutorial:
> [Understanding WebAssembly text format](https://developer.mozilla.org/en-US/docs/WebAssembly/Understanding_the_text_format)

- Text format (wast: **W**eb **AS**sembly **T**ext)
  - S-expression (officially?)
    - comment line  `;; ...` 
    - comment block `(; ... ;)` 

- Types
  - `i32` `i64` `f32` `f64`
  - `[t1*] -> [t2?]` 表示一段代码的 pop 和 push (`<=1` in current ver)

- Func
  - `(func $add ...)`
  - `(export "add" (func $add))`


- Module


Wasm - Export
-----------------

```wast
(module
  (func $add ...)
  (export "add" (func $add))
)
```

shorthand `export`:

```wast
(module
  (func $getAnswer (result i32)
    i32.const 42)
  (func (export "getAnswerPlus1") (result i32)  ;; shorthand export
    call $getAnswer  ;; call function at same module!
    i32.const 1
    i32.add))
```

JS side, use `instance.exports` to use

```js
WebAssembly.instantiateStreaming(fetch('call.wasm'))
 .then(obj => {
    console.log(obj.instance.exports.getAnswerPlus1());  // "43"
  });
```


Wasm - Import
-----------------

Wasm has a _two-level namespace_.
According to spec, the `import` is:

$$
import ::= {module name, name name, desc importdesc}
importdesc ::= func typeidx | table ... | mem ... | global ...
$$

Why `func typeidx` (it's `func funcidx` in `exportdesc`)?
Because they are `hostfunc`:

$$
funcinst ::= {type functype, hostcode hostfunc}   -- 可以看到只有 type
hostfunc ::= ...
$$

```wast
(module
  ;; Import 在 consolo log 之后的其实是一个 functype 的声明，只不过给了 name 方便 refer
  (import "console" "log" (func $log (param i32))) 

  ;; Export 这时 export 的就是 funcidx 了，只不过我们这里用了语法糖，实际上是单独的 func decl 与单独的 export
  (func (export "logIt")
    i32.const 13
    call $log))
```

这种 import 机制不限于 JS，而是通用的。Wasm 从哪知道 `module: "console" name: "log"` 呢？
答案是，JS 这边需要「造」一个这样的结构：

```js
var importObject = {
  console: {                // module
    log: function(arg) {    // name
      console.log(arg);
  }}};

WebAssembly.instantiateStreaming(fetch('logger.wasm'), importObject)
  .then(obj => {
    obj.instance.exports.logIt();  // 13
  });
```


Wasm - Globals
--------------

> global, accessible from both JS and across `WAsm.Module` instances
> this allows _dynamic linking_ of multiple modules

```wast
(module
   (global $g (import "js" "global") (mut i32))   ;; declare a global from imports as mut i32
   (func (export "getGlobal") (result i32)        ;; export getter/setter
        (get_global $g))
   (func (export "incGlobal")
        (set_global $g
            (i32.add (get_global $g) (i32.const 1))))
)
```

make a global from JS side.
同样也是用 `instantiate(module, importObject)` 的 `importObject` 扔进去
WebAssembly JS Interface 会在中间做一层 validation

```js
const global = new WebAssembly.Global({value: "i32", mutable: true}, 0);
```


Wasm - Linear Memory
--------------------

> WebAssembly provides _memory_.
> memory is just a _large array of bytes_ that can grow over time.

### From Wasm, an `i32` address-able

Currently, only *Wasm32* is supported, provides 4GB in total

- `i32.load`  reading and
- `i32.store` writing from linear memory

### From JS, an (resizable) `ArrayBuffer`

```js
function consoleLogString(offset, length) {
  var bytes = new Uint8Array(memory.buffer, offset, length);    // memory.buffer 取出 `ArrayBuffer`
  var string = new TextDecoder('utf8').decode(bytes);
  console.log(string);
}
```

### Interop1 - Wasm Create Memory, Export to JS

然后直接 export 给 JS 侧


### Interop2 - JS Create Memory, Wasm Import

```js
var memory = new WebAssembly.Memory({initial:1});
var importObject = { console: { log: consoleLogString }, js: { mem: memory } };
WebAssembly.instantiateStreaming(fetch('logger2.wasm'), importObject)
  .then(obj => {
    obj.instance.exports.writeHi();
  });
```

```wast
(import "js" "mem" (memory 1))  ;; 1 means i page (Wasm defined it to be 64 KB)
```

### `data` section

```wast
(module
  (import "console" "log" (func $log (param i32 i32)))
  (import "js" "mem" (memory 1))
  (data (i32.const 0) "Hi")         ;; data section，类似 native object file 中的 .data segmentation.
  (func (export "writeHi")
    i32.const 0  ;; pass offset 0 to log
    i32.const 2  ;; pass length 2 to log
    call $log))
```

这里也就是说，让 JS 侧以 `Uint8Array` 的形式解读 Memory，然后取两个 Byte 再以 `utf8` 方式 decode 为 string，刚好就是 `Hi`


Wasm - Tables
------------------

> Tables are basically *resizable arrays of references* that can be accessed by index from WebAssembly code.

可以看到 `call funcidx` take a static func index，是静态派发的
那么如果我们要调用的函数是 *runtime value* （动态派发）怎么办?

比如说:
- First-class Function (e.g. JS)                  => Closure {code_ptr, env_ptr}
- Function Pointer (e.g. C/C++)                   => Fun Ptr {code_ptr}
- Virtual Method/Function/Call  (e.g. C++/Java)   => VTable  {code_ptr, code_ptr, code_ptr...}

所以 Wasm 就有了 `i32.const idx; call_indirect typeidx`
那么这个 `idx` 存哪呢...解决方案就是这个 Table

Hux:
尽管 Closure 也是 funcref，但是由于 Wasm 有特殊的 `Call` 而非 Jump，这部分是可以 typed 到的（比较强的 validation）

### `elem` section and `funcref`

`elem` 类似 `data` 用于定义特殊的静态 section
目前的 `elemtype` 也只有 `funcref` （其实就是 `anyfunc`，需要动态 check）

```wast
(module
  (table 2 funcref)            ;; initial size: 2; elemtype: funcref
  (func $f1 (result i32)
    i32.const 42)
  (func $f2 (result i32)
    i32.const 13)
  (elem (i32.const 0) $f1 $f2) ;; 0 是 offset，因为只能有一个 table，所以可以多次 populate
  ...
)
```

### From JS

```js
function() {
  // table section
  var tbl = new WebAssembly.Table({initial:2, element:"funcref"});

  // function sections:
  var f1 = /* some imported WebAssembly function */
  var f2 = /* some imported WebAssembly function */

  // elem section
  tbl.set(0, f1);
  tbl.set(1, f2);
};
```

### Using the table

由于 `funcref` 是 `anyfunc`，
所以这里我们通过 statically annotate 一个 *presumed type* 到这个 FFI boundary（这样其他部分可以用这个静态信息）
然后通过一个运行时 check 来保证 soundness，如果不 match 的话就 `Trap` (`WebAssembly.RuntimeError`)

```wast
(type $return_i32 (func (result i32)))  ;; if this was f32, (dynamically) type checking would fail
(func (export "callByIndex") (param $i i32) (result i32)
  local.get $i
  call_indirect (type $return_i32))
```

目前只有一个 Table，所以 `call_indirect` 直接 implicitly call `table[0]`
In the future, when multiple tables are allowed:

```wast
(call_indirect $table (type $ft))  ;; folded syntax
```




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
