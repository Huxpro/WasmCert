WasmCert
================================================

A (in-development) Coq mechanization of WebAssembly specification.

For more background information, see the project report literature [Xuan Huang. "A Mechanized Formalization of the WebAssembly Specification in Coq", in _RIT Computer Science_, 20191](https://www.cs.rit.edu/~mtf/student-resources/20191_huang_mscourse.pdf) and/or its [poster presentation](https://www.cs.rit.edu/~mtf/student-resources/20191_huang_mscourse_poster.pdf). 

The report literature is also indexed in [Google Scholar](https://scholar.google.com/scholar?cites=13173623897259187056&as_sdt=2005&sciodt=0,5&hl=en) and [Semantic Scholar](https://www.semanticscholar.org/paper/A-Mechanized-Formalization-of-the-WebAssembly-in-Huang/2fde569f52c37fe8e45ebf05268e1b4341b58cbf#citing-papers) thanks to citations.


Proof atlas
------------------------------------------------

[`site/`](site/) is a small web app that visualizes the proof: what is proved per instruction, how progress and preservation are put together, and which *Software Foundations* chapters teach each proof move. Its progress data is extracted from the `.v` files on every build. See [site/README.md](site/README.md).
