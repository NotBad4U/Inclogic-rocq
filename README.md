# Mechanized Incorrectness Logic in Rocq

A machine-checked development, in the [Rocq Prover](https://rocq-prover.org) (Coq 9.0), of
**Incorrectness Logic** (IL) and related theories, all built on top of a single non-deterministic
IMP language with an explicit `error` command and Kleene Algebra, kept as faithful as possible to
the original papers nothing weakened for the sake of the mechanisation.

## Description

Sound over-approximating methods (e.g. Hoare logic) prove the *absence* of errors, but at the price of false positives — alarms that no real execution exhibits.
Under-approximating methods go the other way: they are aimed at bug finding and are free from false positives. **Incorrectness Logic** (O'Hearn, POPL 2020) is
the formal system for that direction. Its triples

```
[presumption] C [ε: result]
```

read: *every* state satisfying `result` is reachable from *some* state satisfying `presumption` —
the post-assertion is an **under-approximation** of the reachable states, tagged by an exit
condition `ε ∈ {ok, err}`.

This repository provides:

* a non-deterministic **IMP** language extended with an `ERROR` command, non-deterministic choice `c₁ ⊕ c₂` and Kleene iteration `c★`, with `WHILE`/`IF` derived;
* **Incorrectness Logic**: a tag-tracking proof system, its semantic reading, soundness,
  completeness via syntactic strongest postconditions, plus the worked examples of O'Hearn's §6.1;
* **Sufficient Incorrectness Logic**: the backward dual of IL, sound, complete, and related to IL by an adjunction stated and proved;
* an **algebraic view**: IL triples with the TopKAT encoding;
* **Hoare logic**: partial and total correctness, formalised so that its relationship with
  Incorrectness Logic can itself be stated and proved.

### The four triples at a glance

| Notation | Definition | Reading |
|---|---|---|
| `⦃⦃P⦄⦄ c ⦃⦃Q⦄⦄` | `∀ s r, cexec s c r → P s → ∃ s', r = RNormal s' ∧ Q s'` | partial correctness |
| `⦇⦇P⦈⦈ c ⦇⦇Q⦈⦈` / `safe` | from every `P`-state, `c` terminates on every schedule in a `Q`-state | total correctness |
| `⟦⟦P⟧⟧ c ⟦⟦ε ↑ Q⟧⟧` | `∀ r, Q r → ∃ s, P s ∧ cexec s c r` | incorrectness (backward reachability) |
| `⟪⟪P⟫⟫ c ⟪⟪ε ↑ Q⟫⟫` | `∀ s, P s → ∃ r, cexec s c r ∧ Q r` | sufficient incorrectness / Lisbon |

Single brackets (`⟦ ⟧`, `⟪ ⟫`, `⦇ ⦈`) denote the *syntactic* proof systems; doubled brackets denote
their *semantic* counterparts. Soundness and completeness theorems connect the two.

## Installation

### Requirements

| Package | Version used | Also tested with |
|---|---|---|
| `rocq-prover` | 9.2.0 | 9.1.1, 9.0.1 |
| `rocq-mathcomp-ssreflect` | 2.6.0 | 2.5.0 |
| `rocq-mathcomp-finmap` | 2.2.4 | 2.2.2 |
| `rocq-relation-algebra` (for `KatInc.v` / `KatIncImp.v`) | 1.9.0 | 1.8.0 |

### Setup with opam

```sh
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-prover rocq-mathcomp-ssreflect rocq-mathcomp-finmap \
             rocq-hierarchy-builder rocq-relation-algebra
```

### Setup with Nix

The repository is configured with the
[coq-nix-toolbox](https://github.com/rocq-community/coq-nix-toolbox), which pins the whole
dependency set. After [installing Nix](https://nixos.org/download.html), optionally enable the
binary caches once per machine:

```sh
nix-env -iA nixpkgs.cachix && cachix use coq && cachix use coq-community && cachix use math-comp
```

Then, from the root of the repository:

```sh
nix-shell                       # dev shell with rocq, mathcomp, relation-algebra, coq-lsp
nix-build                       # build and install the library into the Nix store
```

Three *bundles* are defined in [`.nix/config.nix`](.nix/config.nix): `9.2` (the default, matching
the versions in the table above), `9.1` and `9.0`. Select one with `--argstr bundle`, e.g.

```sh
nix-shell --argstr bundle 9.0
nix-build --argstr bundle 9.0
```

Useful commands available inside the shell: `nixHelp`, `ppNixEnv` (list the packages and their
versions), `ppBundles`, `cachedMake`, `genNixActions` (regenerate the GitHub Actions workflows in
[`.github/workflows/`](.github/workflows), one per bundle).

Two overlays live in [`.nix/rocq-overlays/`](.nix/rocq-overlays):
[`inclogic`](.nix/rocq-overlays/inclogic/default.nix) describes this development, which is not in
nixpkgs, and [`relation-algebra`](.nix/rocq-overlays/relation-algebra/default.nix) adds release
1.9.0 — the first to support Rocq 9.2 — which nixpkgs does not carry yet.

### Build

```sh
make                                       # build everything
make -j4                                   # parallel build
make clean
make html                                  # generate the documentation (run `rocq doc`) 
make install
```

The tracked [`Makefile`](Makefile) is a thin wrapper: it runs `rocq makefile` on
[`_CoqProject`](_CoqProject) — which maps `theories/` to the `IncLogic` logical path — to produce
`Makefile.coq`, and forwards every target to it. `Makefile.coq`, `Makefile.coq.conf` and
`.Makefile.coq.d` are generated files that bake in the absolute paths of the toolchain they were
produced with, so they are gitignored and rebuilt on demand. A plain `make` therefore works in any
of the environments above — opam or `nix-shell` — with no manual step.

Compiling [`theories/Assumptions.v`](theories/Assumptions.v) runs `Print Assumptions` on every main
theorem. All of them report **`Closed under the global context`**: the development depends on no
axiom.

## Organization

The files are listed in dependency order (the order of `_CoqProject`).

| File | Content |
|---|---|
| [`theories/Sequences.v`](theories/Sequences.v) | Generic library on transition relations: `star` (reflexive-transitive closure), `plus`, `irred`, `infseq` and its coinduction principle, determinism/uniqueness lemmas. |
| [`theories/RelKleene.v`](theories/RelKleene.v) | Kleene-algebra layer over `Sequences`: extensional relation equality `≡`, composition `⨟`, `Proper` instances so `rewrite` traverses `star`/`plus`, and the Kleene laws (`star_idem`, unfoldings, `star_star`). |
| [`theories/Imp.v`](theories/Imp.v) | The IMP language. `Choice`/`Countable` instances for `ascii`/`string` (so `store := {fmap string → Z}` typechecks), syntax `aexp`/`bexp`/`com`, `result = RNormal | RError`, small-step `red`, big-step `cexec`, `WHILE`/`IF` as derived forms, `CSTAR` ↔ `star (step_iter c)`, and the equivalence `cexec ↔ star red`. |
| [`theories/Hoare.v`](theories/Hoare.v) | Hoare logic. Weak triple `⦃⦃ ⦄⦄`, strong system `⦇ ⦈` (well-founded `CSTAR` variant rule), demonic `Triple` `⦇⦇ ⦈⦈`. Modules: `Soundness`, `Completness` (semantic `wlp`, self-invariant `CSTAR`, adequacy), `WP` and `SP` (verification-condition generators), `TotalCorrectness` (inductive `safe`, `TotalTriple`, soundness/completeness/adequacy). |
| [`theories/Inc.v`](theories/Inc.v) | Incorrectness Logic. `tag = TOk \| TErr` and `lift` to make O'Hearn's `ε` metavariable explicit, the inductive `Inc_triple` `⟦ ⟧`, derived forward/backward-variant/choice/consequence rules, semantic `IncTriple` `⟦⟦ ⟧⟧`. Modules: `SPre`, `IncSoundness` (`Inc_triple_sound`), `IncCompleteness` (syntactic `spo`/`spe`, `Inc_complete`), `SP` (strongest-post generator). |
| [`theories/Sil.v`](theories/Sil.v) | Sufficient Incorrectness Logic. Inductive `Sil_triple` `⟪ ⟫` (with a `nat`-indexed invariant for `CSTAR`), semantic `SilTriple` `⟪⟪ ⟫⟫`, `StrongTriple` bridge, `sil_eq_total_hoare_det`. Modules: `Wp` (backward image, computed by inversion), `SilSoundness`, `SilCompleteness`; plus the IL↔SIL connection `sp_wp_adjoint` and the dual distribution laws. |
| [`theories/ExampleInc.v`](theories/ExampleInc.v) | The four programs of Figure 5 / §6.1 of O'Hearn's paper (`loop0`, `client0`, `loop1`, `loop2`) with their IL triples proved, plus `ok`-shaped variants of the sequence/consequence/backwards-variant rules used by the examples. |
| [`theories/KatInc.v`](theories/KatInc.v) | IMP over **Kleene Algebra with Tests** (`RelationAlgebra`): `prog` syntax, relational `bstep`, its inductive counterpart `bstep'`, the `kat` tactic deriving Hoare rules, and the TopKAT-style encoding of incorrectness triples. |
| [`theories/KatIncImp.v`](theories/KatIncImp.v) | The bridge: `prog'` (KAT programs with syntactic expressions), translations `to_com` / `to_kat`, the proof that `bstep` and `cexec` agree on normal results, and the lifting of `Incorrectness` to `IncTriple`. |
| [`theories/Assumptions.v`](theories/Assumptions.v) | `Print Assumptions` for every headline theorem of `Hoare`, `Inc` and `Sil` — the axiom-freeness check. |
| [`theories/StateMap.v`](theories/StateMap.v) | Legacy `FMapWeakList`-based store, superseded by the mathcomp `finmap` store in `Imp.v`. Not part of `_CoqProject`; contains `Admitted` lemmas. |
| [`Docs/`](Docs/) | Background slides and notes (Hoare logic course, IL, abstract interpretation, WP/Frama-C, `wp`/`sp`). |

### Main theorems

| Theorem | Location |
|---|---|
| `triple_soundness`, `Triple_soundness` | `Hoare.Soundness` |
| `Hoare_complete`, `Hoare_adequate` | `Hoare.Completness` |
| `vcgen_sound` (weakest precondition / strongest postcondition) | `Hoare.WP`, `Hoare.SP`, `Inc.SP` |
| `TotalTriple_soundness`, `TotalTriple_complete`, `TotalTriple_adequate` | `Hoare.TotalCorrectness` |
| `Inc_triple_sound` | `Inc.IncSoundness` |
| `Inc_complete` | `Inc.IncCompleteness` |
| `Sil_triple_sound` | `Sil.SilSoundness` |
| `Sil_complete` | `Sil.SilCompleteness` |
| `sp_wp_adjoint`, `sil_eq_total_hoare_det` | `Sil` |

## Bibliographie

1. Peter W. O'Hearn. **Incorrectness Logic**. *Proc. ACM Program. Lang.* 4, POPL, Article 10
   (January 2020), 32 pages. <https://doi.org/10.1145/3371078> — the reference for
   [`Inc.v`](theories/Inc.v) and [`ExampleInc.v`](theories/ExampleInc.v).
2. Flavio Ascari, Roberto Bruni, Roberta Gori, Francesco Logozzo. **Sufficient Incorrectness Logic:
   SIL and Separation SIL**. arXiv:2310.18156, 2023–2024. <https://arxiv.org/abs/2310.18156> — the
   reference for [`Sil.v`](theories/Sil.v).
3. Cheng Zhang, Arthur Azevedo de Amorim, Marco Gaboardi. **On Incorrectness Logic and Kleene
   Algebra with Top and Tests**. *Proc. ACM Program. Lang.* 6, POPL (January 2022).
   <https://doi.org/10.1145/3498690> — the TopKAT encoding used in
   [`KatInc.v`](theories/KatInc.v).
4. Bernhard Möller, Peter W. O'Hearn, Tony Hoare. **On Algebra of Program Correctness and
   Incorrectness**. RAMiCS 2021. <https://doi.org/10.1007/978-3-030-88701-8_20> — Lisbon triples,
   the angelic reading behind SIL.
5. C. A. R. Hoare. **An Axiomatic Basis for Computer Programming**. *Comm. ACM* 12(10), 1969.
   <https://doi.org/10.1145/363235.363259>
6. Edsger W. Dijkstra. **Guarded Commands, Nondeterminacy and Formal Derivation of Programs**.
   *Comm. ACM* 18(8), 1975. <https://doi.org/10.1145/360933.360975> — the `wp` calculus of
   `Hoare.WP`.
7. Xavier Leroy. **Proving the Correctness of a Compiler** (EUTypes 2019 summer school, lecture
   notes and Coq development). <https://xavierleroy.org/courses/EUTypes-2019/> — the IMP language,
   `Sequences.v` and the small-step/big-step equivalence follow this development.
8. Damien Pous. **Kleene Algebra with Tests and Coq Tools for While Programs**. ITP 2013.
   <https://doi.org/10.1007/978-3-642-39634-2_15> — the `RelationAlgebra` library and the `imp`
   example that [`KatInc.v`](theories/KatInc.v) adapts.
9. Quang Loc Le, Azalea Raad, Jules Villard, Josh Berdine, Derek Dreyer, Peter W. O'Hearn.
   **Finding Real Bugs in Big Programs with Incorrectness Logic**. *Proc. ACM Program. Lang.* 6,
   OOPSLA1 (2022). <https://doi.org/10.1145/3527325>
