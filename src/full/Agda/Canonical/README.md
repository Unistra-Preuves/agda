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
{! [timeout] [(count := n)] [+debug] [[lem₁, lem₂, …]] !}
```

| Option | Default | Meaning |
|---|---|---|
| `timeout` (leading number, or `(timeout := n)`) | `5` | Search time limit, in seconds. |
| `(count := n)` | `1` | Number of solutions to search for. The first one accepted by Agda is written. |
| `+debug` | off | Only display the problem sent to Canonical and its solutions, without writing anything. |
| `[lem₁, lem₂, …]` | `[]` | Names added to Canonical's context before the local variables. |

Examples:

```agda
{! !}                              -- 5 s, one solution
{! 10 !}                           -- 10 s
{! (count := 3) !}                 -- three solutions
{! 2 (count := 3) [+-comm, cong] !}
{! +debug !}                       -- display only
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

The Lean flags other than `+debug` (`+synth`, `-simp`, …) are rejected with an error message: the
Agda interface (`canonical_solve`, from the `canonical-agda` crate) only
exposes the timeout and the number of solutions.

## Output

Without `+debug`, the first solution accepted by Agda is written in the file:

- **Case split.** If the solution is a recursor applied to a variable of the
  clause (e.g. `f n = ?`), the clause is split on that variable as with
  `C-c C-c`. If it is applied to an argument of the goal (e.g. `f = ?`, with
  the answer `λ xs ys → D.rec … xs`), the arguments are first introduced as
  patterns, as `C-c C-c` without variables does. Each new clause gets its
  right-hand side, and induction hypotheses become recursive calls with the
  other arguments of the clause:

  ```agda
  vlen-ok [] = refl
  vlen-ok (x ∷ v) = refl
  ```

  Implicit fields that Agda leaves out of the patterns are added (`{n}`) when
  the right-hand side needs them.
- **Term.** Otherwise the hole is filled with the term, without implicit
  arguments. If this leaves unsolved metas or constraints, the term is given
  again with all implicit arguments in braces (`q {zero}`).
- **Nothing accepted.** If Agda rejects every solution, or they all leave
  something unsolved, nothing is written: the solutions are displayed with the
  reason.

`C-c C-g` outside a hole solves all goals, one second each, without case
splits.

Terms are printed as follows:

- implicit arguments of applications are omitted (Agda infers them), unless
  needed as explained above;
- implicit binders (`λ {A} → …`, `{n}` in patterns) are kept, in braces, only
  when they are used;
- `Pi`, `Pi.mk` and `Pi.f` are printed back as `(x : A) → B`, `A → B`, `λ` and
  application; `Type l` is printed as `Set`, `Set₁`, … or `Set l`;
- other recursors become pattern-matching lambdas. Agda cannot infer the type
  of a pattern-matching lambda applied to an argument, so the motive found by
  Canonical is given in a `let` (indices are matched with `_`):

  ```agda
  +zero (suc n) = let r : (a : Nat) → (n + zero) ≡ a → suc (n + zero) ≡ suc a
                      ; r = λ { _ refl → refl } in r n (+zero n)
  ```

- variable names lose the `.N` suffix added during translation, and get primes
  when they would shadow a name in scope.

### Limitations

- A case split is only done when the recursor is at the top of the answer,
  on an explicit variable. Otherwise the solution is given as a term, in which
  an induction hypothesis becomes a recursive call on the field alone; Agda
  rejects it when the function has other arguments (the error is displayed).
- The context variables that cannot be referred to (shown "not in scope", such
  as the implicit arguments introduced by Agda in `f = ?`) are printed `_`,
  and left to Agda.
- The clauses of a case split cannot be checked before being written; Agda
  checks them when the file is reloaded.
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

The crate lives in the [Canonical repository](https://github.com/Unistra-Preuves/Canonical),
not in Agda. Agda does not link against it: the library is loaded at the first
`C-c C-g`, so Agda builds without it. Build it with `python3 build_agda.py` in
that repository, then either set `AGDA_CANONICAL_LIB` to the path of
`lib/libcanonical_agda.so` (`.dylib` on macOS, `canonical_agda.dll` on
Windows), or add its directory to the library search path (`LD_LIBRARY_PATH`,
`DYLD_LIBRARY_PATH`, `PATH`). If the library cannot be loaded, `C-c C-g`
displays the reason.
