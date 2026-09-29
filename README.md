WasmCert
================================================

A (in-development) Coq mechanization of WebAssembly specification.

For more background information, see the project report literature [Xuan Huang. "A Mechanized Formalization of the WebAssembly Specification in Coq", in _RIT Computer Science_, 20191](https://www.cs.rit.edu/~mtf/student-resources/20191_huang_mscourse.pdf) and/or its [poster presentation](https://www.cs.rit.edu/~mtf/student-resources/20191_huang_mscourse_poster.pdf). 

The report literature is also indexed in [Google Scholar](https://scholar.google.com/scholar?cites=13173623897259187056&as_sdt=2005&sciodt=0,5&hl=en) and [Semantic Scholar](https://www.semanticscholar.org/paper/A-Mechanized-Formalization-of-the-WebAssembly-in-Huang/2fde569f52c37fe8e45ebf05268e1b4341b58cbf#citing-papers) thanks to citations.


Building
------------------------------------------------

The development builds with Coq 8.18:

```sh
make -C coq
```

Type soundness
------------------------------------------------

`coq/Soundness.v` proves type soundness of the formalized subset (numeric,
parametric and structured control instructions): a valid configuration never
gets stuck. Every configuration it reduces to is still valid, and is either a
result (values or a trap) or can take a step.

```coq
Theorem soundness : forall S T S' T' rt,
    ⊢c (S, T) ∈ rt ->
    ($(S, T)) ↪* ($(S', T')) ->
    ⊢c (S', T') ∈ rt /\
    (⊢R T' ∈ rt \/ exists S'' F'' ainstrs'', $(S', T') ↪ (S'', F'', ainstrs'')).
```

Integer operators are defined on top of Coq's `ZArith`, following the spec's
numerics. Float operators are still left abstract. `coq/check-assumptions.sh`
checks that the theorem assumes nothing beyond those operators.
