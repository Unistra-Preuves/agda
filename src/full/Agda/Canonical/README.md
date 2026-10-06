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
| `Induction.hs` | Induction hypotheses of a goal in a clause that matches a constructor. |
| `Recursor.hs` | Generation of a recursor `D.rec` for each datatype. |
| `Builtin.hs` | Declarations that do not come from Agda: `Type`, the `Pi` encoding, the `_⊔_` rules. |
| `FFI.hs` | Exchange with the Rust crate `canonical-agda` (`runCanonical`), see [Interface with Rust](#interface-with-rust). |
| `FromCanonical.hs` | Printing of the answers in Agda syntax (`cexprToAgda`). |
| `Types.hs` | The intermediate language (`CDecl`, `CExpr`, `CSpine`, `CEquation`) and the signatures. |
| `Utils.hs` | Fresh names and η-expansion. |
| `Cubical.hs` | Cubical Agda: paths as functions of the interval, the interval and its primitives, `Path.mk`/`Path.f`. |

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
| `+debug` | off | Only display the problem sent to Canonical and its solutions, without writing anything. Variables that are not in scope are shown under their names. |
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

### Induction hypotheses

In a clause that matches constructors, the recursive calls on the variables
bound under them are added to Canonical's context. For instance, in

```agda
addcomm (S n) (S m) = {! !}
map f (x ∷ xs) = {! !}
```

Canonical may use `addcomm n (S m)`, `addcomm (S n) m`, `addcomm n m`,
`addcomm m n`, … and `map f xs`. A call replaces some explicit arguments of
the clause by smaller variables and keeps the others; when that call is
ill-typed (an index changes, as in `len (suc n) (x ∷ xs)`), the arguments that
are not variables are inferred instead (`len n xs`). A call is kept only if it
terminates according to the size-change criterion of Agda's termination
checker. With `+debug`, these calls are listed under
`--- Induction hypotheses`.

A recursor that is not split on is printed as a pattern-matching lambda, which
is not recursive: a solution that uses its induction hypothesis is rejected.

### Cubical Agda

When the file uses `--cubical`, the translation is adapted (see `Cubical.hs`):

- In a type position, a path type `PathP A x y` (or `x ≡ y`) becomes
  `(i : I) → A i`, and a declaration of that type gets its boundary
  `p i0 ⤇ x`, `p i1 ⤇ y`: rewrite rules for the context and the definitions,
  constraints for the parameters. A path application `p i` is an ordinary
  application.
- `IUniv`, `I`, `i0`, `i1` are declared (`I` without recursor), as well as
  `_∧_`, `_∨_`, `~_` with their computation rules and the De Morgan laws.
  They are printed under the names they have in scope.
- A path type occurring as a term is kept as `PathP`, with `Path.mk` and
  `Path.f` to build and apply its values (as `Pi.mk` and `Pi.f`).
- A goal of path type is stated through a continuation, so that its boundary
  is checked by Canonical (see below). A path of functions
  (`f ≡ g`) is treated as a function to paths, and a square as a path to
  paths, so that the boundary in the first dimension is closed: `funExt`
  gives `λ i x → h x i`, a connection `λ i j → p (j ∧ i)`.
- In a clause with interval variables (`f p i = ?`, `f p i a = ?`), the
  context is refolded into the type of the goal, from the first interval
  variable constrained by the boundary of the hole: an interval variable with
  its two faces becomes a path type again (`B a` with `i = i0 ⊢ f a`,
  `i = i1 ⊢ g a` becomes `f ≡ g`), the other variables Π-binders. This goal
  is translated as above, and the binders of the solution that stand for the
  refolded variables are unfolded back into them: `funExt p i a = p a i`,
  `conn p i j = p (j ∧ i)`. Faces fixing several variables at once are
  ignored.
- A hole may also be constrained by unification constraints of Agda in which
  its meta is applied to the context with some variables substituted, e.g.
  `p (?0 (i = i1)) = x` and `p (?0 (i = i0)) = y` for `sym p i = p ?`. The
  context is then refolded from the first substituted variable, and the
  solution `g` (here `g : I → I`) gets the constraints `p (g i1) ⤇ x`,
  `p (g i0) ⤇ y`, which gives `~ i`. Only the constraints whose context is
  a prefix of the context of the hole, and that do not mention a refolded
  variable outside of the meta, are used.

Canonical does not apply a symbol that has a non-linear rule, so `_∧_` and
`_∨_` have no idempotence rule: solutions may contain `i ∧ i`.

### Goals with metas

The type of the goal may contain unsolved metas, e.g. `add _ _ ≡ S Z`, in any
number. Canonical then looks for their values too, following an encoding
suggested by Chase Norman: each meta, a function of the context in which it
was created, becomes an existential variable of its closed type, bound by a
continuation

```
Goal : Δ → (k : (?m₁ : A₁) … (?mₙ : Aₙ) → (S : Type l) → S → G) → G
```

with the constraint `S ≡ B` on `S`, where `Δ → B` is the type of the goal (`Δ`
being its longest prefix without metas) and `G` a fresh opaque type. (The same
continuation, with `g : Θ → B` and constraints on `g`, states the boundary of
paths and of cubical holes: Canonical only checks constraints on parameters.) A meta
whose type contains other metas comes after them. The binders `Δ` are in
fact declared in the context, as the variables introduced by Agda, and the
goal is only `(k : …) → G`: the equations of a parameter are only constraints
on its instances, so the boundary of a path in `Δ` (e.g. `p x i0 ⤇ f x` for
`p : (x : A) → f x ≡ g x` in `funExt = ?`) would not be a rewrite rule. A
goal with a parameter of path type is therefore always stated through a
continuation. From the answer `λ k → k t₁ … tₙ B b`, each meta `?mᵢ` is
assigned `tᵢ`, then `λ Δ → b` is given. A value that Agda rejects (e.g. a name out of scope) is skipped: Agda
may still find the meta by unification. With `+debug`, the values are shown
after the hint (`with _14 := S Z`).

Metas in the types of the context are not supported. A clause whose body
still contains a hole is not given to Canonical as a rewrite rule.

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
- **Clause.** The term is written in the clause rather than given when the
  hole is the whole right-hand side and the term is accepted (or only leaves
  something unsolved), in two cases, possibly together:
  - the term is a λ: its binders become patterns, `f x = b` rather than
    `f = λ x → b` (unused explicit binders become `_`, unused implicit ones
    are left out);
  - it uses context variables that cannot be referred to (shown "not in
    scope", such as the implicit arguments introduced by Agda in `f = ?`):
    they are made visible, as `C-c C-c` on them does.

  ```agda
  refl {a = a} _ = a          -- instead of  refl = λ _ → _
  sym p i = p (~ i)           -- instead of  sym = λ p i → p (~ i)
  ```

  The new clause is not checked before being written.
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
- The context variables that cannot be referred to are printed `_`, and left
  to Agda, when they cannot be made visible (module parameters, hidden
  λ-bound variables), in case splits, when all goals are solved at once, and
  when the hole is not the whole right-hand side (`f x = g ?`). In the last
  two cases, a λ is also given as it is.
  With `+debug`, the hints show them under their names.
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
