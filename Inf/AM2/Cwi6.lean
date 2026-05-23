import Mathlib.Topology.Metrizable.Uniformity

open Topology Filter

namespace AM2.Cwi6

theorem Zad4 [MetricSpace X] {x : X} : IsClosed {x} := isClosed_singleton

alias Zad5_a := IsOpen.inter
alias Zad5_b := isOpen_iUnion
/-- Note that this fails to hold when `ι` is infinite. -/
alias Zad5_c := isOpen_iInter_of_finite
