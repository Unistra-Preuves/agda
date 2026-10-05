# Canonical in Agda

[Canonical](https://chasenorman.com) is an exhaustive proof search tool for
dependent type theory. This directory connects it to Agda's interactive mode:
`C-c C-g` translates the goal and its context for Canonical, calls the solver
through the FFI, and prints the solution as Agda syntax.

| File | Contents |
|---|---|
| `Canonical.hs` | Entry point of `C-c C-g` (`callCanonical`): options, lemmas, and the whole pipeline. |
| `Options.hs` | Options written in the hole, and their parser. |
| `ToCanonical.hs` | Translation of the goal, its context and the definitions it uses. |
| `Recursor.hs` | Generation of a recursor `D.rec` for each datatype. |
| `Builtin.hs` | Declarations that do not come from Agda: `Type`, the `Pi` encoding, the `_⊔_` rules. |
| `FFI.hs` | Exchange with the Rust crate `canonical-agda` (`runCanonical`), see [Interface with Rust](#interface-with-rust). |
| `FromCanonical.hs` | Printing of the answers in Agda syntax (`cexprToAgda`). |
| `Types.hs` | The intermediate language (`CDecl`, `CExpr`, `CSpine`, `CEquation`) and the signatures. |
| `Utils.hs` | Fresh names and η-expansion. |
| `Cubical.hs` | Draft of the cubical support; not compiled. |

## Usage

Put the cursor in a hole and press `C-c C-g`. Options are written inside the
hole, in the same format as the Lean `canonical` tactic:

```
{! [timeout] [(count := n)] [[lem₁, lem₂, …]] !}
```

| Option | Default | Meaning |
|---|---|---|
| `timeout` (leading number, or `(timeout := n)`) | `5` | Search time limit, in seconds. |
| `(count := n)` | `1` | Number of solutions to search for. With more than one, they are listed under `--- Hints`. |
| `[lem₁, lem₂, …]` | `[]` | Names added to Canonical's context before the local variables. |

Examples:

```agda
{! !}                              -- 5 s, one solution
{! 10 !}                           -- 10 s
{! (count := 3) !}                 -- three solutions
{! 2 (count := 3) [+-comm, cong] !}
```

### Lemmas

- A lemma can be a definition, a postulate, a constructor or a projection.
  Each name is resolved in the scope of the hole. Definitions bring their
  clauses with them (as rewrite rules), and datatypes bring their constructors
  and their generated recursor.
- An unknown name raises Agda's usual scope error. A local variable is
  rejected: it is already in the context.
- The lemma list must come last, because a name such as `[]` may appear in it.
- Separate lemmas with `, ` (comma followed by a space), as in Lean. Agda names
  may contain commas (`_,_`), so a comma without a following space is only
  treated as a separator when the word contains no `_`.

### Unsupported options

The Lean flags (`+synth`, `-simp`, …) are rejected with an error message: the
Agda interface (`canonical_solve`, from the `canonical-agda` crate) only
exposes the timeout and the number of solutions.

## Output

The answer is printed as an Agda term:

- implicit arguments of applications are omitted (Agda infers them);
- implicit binders (`λ {A} → …`, `{n}` in patterns) are kept, in braces, only
  when they are used in the printed term;
- `Pi`, `Pi.mk` and `Pi.f` are printed back as `(x : A) → B`, `A → B`, `λ` and
  application; `Type l` is printed as `Set`, `Set₁`, … or `Set l`;
- recursors `D.rec` are turned into pattern-matching lambdas
  `(λ { c₁ x → … ; c₂ y → … }) major`; unused fields become `_`;
- variable names lose the `.N` suffix added during translation, and get primes
  when they would shadow a name in scope.

Example, for `+zero : (n : Nat) → n + zero ≡ n`:

```agda
(λ { zero → refl ; (suc a) → (λ { refl → refl }) (+zero a) }) n
```

### Limitations

- Pattern-matching lambdas are not recursive. When a branch uses an induction
  hypothesis, it is printed as a recursive call to the function containing the
  hole (`rec` if unknown). The result then reads as the clauses to write rather
  than as a valid term.
- That recursive call only receives the recursive field: for
  `+suc : (n m : Nat) → …` one gets `+suc a` instead of `+suc a m`.
- The visibility of variables bound inside the answer is unknown, so they are
  assumed explicit.
- Anonymous binders (`A → B`) are printed as `a`, `a'`, `a''`, …

## Interface with Rust

`FFI.hs` and `Canonical/crates/canonical-agda/src/lib.rs` exchange terms as
trees of C structs, with no serialisation:

- arrays are `(pointer, length)` pairs of contiguous structs, and strings are
  UTF-8 bytes without terminator;
- the goal is written by Haskell in a memory pool, read by Rust during
  `canonical_solve` (Rust builds its own IR from it), and freed when the call
  returns;
- the solutions are allocated by Rust in the same layout, read by Haskell, then
  released with `canonical_free`;
- if the search panics, `canonical_solve` returns a null pointer, which Haskell
  reads as "no solution".

The layout is described at the top of both files. Haskell computes the offsets
from the size of a pointer, and the Rust side checks the same sizes and offsets
at compile time. Any change to the structs must be made on both sides.

After modifying the crate, rebuild it with `cargo build -p canonical-agda` in
`Canonical/`: Agda links against `Canonical/target/debug/libcanonical_agda.so`.
