/-!
# Core GIP Types

This file defines the absolute foundational types for the GIP project,
such as the `Origin` and its `Aspect`s. It is designed to have no
other dependencies within the `Gip` namespace, allowing other files
to import it without creating circular dependencies.
-/

namespace GIP.CoreTypes

-- Note: The `open GIP.Obj` was removed as it came from the conflicting `Gip.Core`
-- and is no longer needed.

/-- The three aspects through which the origin manifests -/
inductive Aspect : Type where
  | empty : Aspect      -- ∅: Initial limit, empty of constraints
  | identity : Aspect   -- n: Knowable register, determination
  | infinite : Aspect   -- ∞: Terminal limit, infinite capacity
  deriving Repr, DecidableEq

/-- The type of the Origin itself. -/
axiom OriginType : Type

/-- An axiom asserting the existence of a single, unique term for the Origin. -/
axiom the_origin : OriginType

/-- An axiom asserting that any term of OriginType is equal to `the_origin`. -/
axiom origin_is_unique : ∀ o : OriginType, o = the_origin

/--
A manifestation of the Origin as one of its Aspects. For example,
`manifest the_origin Aspect.empty` is the type of the empty set aspect.
-/
axiom manifest (orig : OriginType) (a : Aspect) : Type

end GIP.CoreTypes
