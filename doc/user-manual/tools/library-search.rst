.. _library-search:

**************
Library Search
**************

Agda can search the loaded libraries for a lemma that proves the current
goal.  The two commands are modelled after Lean's ``exact?`` and ``apply?``.

Usage
=====

Both commands are run on an empty hole.

``exact?`` (:kbd:`C-c C-x C-e`, ``Cmd_exact_search``)
  Looks for a lemma that closes the goal and fills the hole with it,
  for instance ``+-comm a b``.  The explicit arguments of the lemma that
  unification does not determine are filled with local variables and
  constructors (such as ``refl``), up to a small depth.

``apply?`` (:kbd:`C-c C-x C-p`, ``Cmd_apply_search``)
  Lists the lemmas whose conclusion unifies with the goal, best first.
  Each suggestion is printed with a ``?`` for every remaining subgoal,
  followed by the types of these subgoals, so that it can be pasted into
  the hole and refined further.

For example, in::

  t : (a b c : ℕ) → a ≤ b → b ≤ c → a ≤ c
  t a b c p q = {! !}

``exact?`` fills the hole with ``≤-trans p q``, while for the goal
``a ≤ c`` with no hypotheses ``apply?`` suggests (among others)
``≤-trans ? ?`` with the subgoals ``? : a ≤ _n`` and ``? : _n ≤ c``,
where ``_n`` is a metavariable that the two subgoals share.

How it works
============

1. **Candidates.**  The search considers the definitions in scope at the
   hole and the publicly exported definitions of every (transitively)
   imported module, even if they are not in scope.  A suggestion using a
   lemma that is not in scope is shown, but not inserted: its module has
   to be imported or opened first.  Generated definitions, module
   applications that are not in scope and the function being defined are
   skipped.

2. **Filtering.**  The conclusion of each candidate (its type without the
   leading Π-binders, after reduction to weak head normal form) is
   summarised by its head symbol and the head symbols of its visible
   arguments, up to a fixed depth.  Only the candidates whose summary
   matches the goal are tried, the most specific ones first.  Lemmas whose
   conclusion matches every goal, like ``⊥-elim : ⊥ → A`` or
   ``sym : x ≡ y → y ≡ x``, are dropped.

3. **Unification.**  A candidate is applied to fresh metavariables and its
   type is compared to the goal type.  Candidates that leave unsolved
   constraints are rejected.  The remaining explicit arguments become
   subgoals, which a bounded search tries to close with the local
   variables and the constructors of their types.

Before looking at the library, ``exact?`` tries to close the goal with
the local variables and constructors alone.

The search is bounded in time (5 seconds of CPU time) and, for
``apply?``, in the number of suggestions (20).

Limitations
===========

* The search does not introduce λ-abstractions: a goal of the shape
  ``∀ x → P x`` is matched against the lemmas with the same number of
  binders.

* The content of the hole is ignored.

* The summaries compare terms syntactically below the head symbol, so
  a lemma about ``n + 0`` is not found for a goal about ``n``, even if
  the two are definitionally equal.
