import Mathlib.Topology.Basic
import Mathlib.Data.Real.Basic

-- Test that mathlib is working with topological spaces
#check TopologicalSpace
#check Continuous
#check IsOpen

-- Test simple topology on a type
variable {X : Type*} [TopologicalSpace X]
#check IsOpen (Set.univ : Set X)
