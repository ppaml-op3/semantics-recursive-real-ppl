# Contextual Equivalence for a Language with Continuous Random Variables and Recursion

Coq development of theorems and proofs.

Requirements:

- Coq 8.6
- [Autosubst](https://github.com/uds-psl/autosubst)
- [Coquelicot](http://coquelicot.saclay.inria.fr/)

Coquelicot may require additional dependencies that we do not rely on directly.

To build, use `make` or run using ProofGeneral.


# File layout

- `Basics.v`: Non-domain specific tactics and hints for auto.
- `Measures.v`: Axioms about measure theory and lemmas about measure theory and
  real analysis.
- `Syntax.v`: The syntax and static semantics of programs and related lemmas.
- `OpSem.v`: The operational semantics for execution using a single entropy.
- `MeasSem.v`: The measure semantics
- `LogRel.v`: The definition of the logical relation.
- `Compatibility.v`: The compatibility lemmas and the fundamental theorem for
  the logical relation.
- `CIU.v`: The definition of the CIU `CIU` relation and the proof of equivalence
  with the E relation `Erel`.
- `CTX.v`: Direct and indirect definitions of contextual ordering, the proof of
  the equivalence of those relations, and the proof of equivalence with `Erel`
  and `CIU`.
- `Interpolation.v`: The interpolation and genericity theorems for manipulating
  small-step semantics as if they were big-step semantics.
  preserve measure.
- `EntropyShuffling.v`: Lemmas about Entropy reshufflings that preserve measure.

# Acknowledgment

This material is based upon work sponsored by the Air Force Research Laboratory
(AFRL) and the Defense Advanced Research Projects Agency (DARPA) under Contract
No. FA8750-14-C-0002. The views expressed are those of the authors and do not
reflect the official policy or position of the Department of Defense or the
U.S.  Government.
