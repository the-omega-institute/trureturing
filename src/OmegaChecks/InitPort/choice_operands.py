"""Check pinned selectors used by public Init declarations against their Lean certificates."""

CHOICE_TYPE_OPERANDS = {
    ("Init.Internal.Order.While", "repeatM.Internal.eq_of_monadTail"):
        ("repeatM", "OmegaChecks.InitBoundaries.choiceFromRepeatM"),
    ("Init.Internal.Order.While", "Lean.Loop.forIn_eq_of_monadTail"):
        ("Lean.Loop.forIn", "OmegaChecks.InitBoundaries.WhileChoice.choiceFromLoop"),
    ("Init.Grind.Injective", "Lean.Grind.leftInv_eq"):
        ("Lean.Grind.leftInv", "OmegaChecks.InitBoundaries.choiceFromLeftInv"),
    ("Init.Control.Lawful.MonadAttach.Lemmas", "WeaklyLawfulMonadAttach.bind_attach_of_nonempty"):
        ("Classical.ofNonempty", "OmegaChecks.InitBoundaries.choiceFromOfNonempty"),
    ("Init.Classical", "Classical.epsilon_singleton"): ("Classical.epsilon", "OmegaChecks.InitBoundaries.choiceFromEpsilon"),
    ("Init.Data.Range.Polymorphic.RangeIterator", "Std.Rxc.Iterator.instIteratorLoop.loop.eq_1"):
        ("WellFounded.extrinsicFix₃", "OmegaChecks.InitBoundaries.choiceFromFix₃"),
}

for owner, equation, arity in (
    ("Init.Data.Iterators.Consumers.Access", "Std.Iter.atIdxSlow?.eq_1", "₂"),
    ("Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect", "Std.IterM.toListRev.go.eq_1", "₂"),
    ("Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect", "Std.IterM.toArray.go.eq_1", "₂"),
    ("Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop", "Std.IterM.DefaultConsumers.forIn'.eq_1", "₃"),
    ("Init.Data.Range.Polymorphic.RangeIterator", "Std.Rxo.Iterator.instIteratorLoop.loop.eq_1", "₃"),
    ("Init.Data.Range.Polymorphic.RangeIterator", "Std.Rxi.Iterator.instIteratorLoop.loop.eq_1", "₃"),
):
    CHOICE_TYPE_OPERANDS[owner, equation] = (
        "WellFounded.extrinsicFix" + arity, "OmegaChecks.InitBoundaries.choiceFromFix" + arity)


def choice_type_dependencies(certificates):
    result = {}
    for owner, name, operand, witness in certificates:
        site = owner, name
        if CHOICE_TYPE_OPERANDS.get(site) != (operand, witness) or site in result:
            raise ValueError(f"invalid choice operand certificate for {site}")
        result[site] = operand
    return result


SPECIFIED_SELECTION = {
    ("Init.Data.Option.Lemmas", "Option.choice_eq_" + suffix):
        ("Option.choice", "Option.isSome_choice", "OmegaChecks.InitBoundaries.OptionSelector.fromSome")
    for suffix in ("some", "default")
} | {
    ("Init.Internal.Order.Basic", "Lean.Order.flat_csup_" + suffix):
        ("Lean.Order.flat_csup", "OmegaChecks.InitBoundaries.InternalOrder.officialFlatPresence",
         "OmegaChecks.InitBoundaries.InternalOrder.choiceFromFlatPresence")
    for suffix in ("eq", "is_sup")
}


def specified_choice_sites(checks, rows):
    sites = {}
    reductions = {(r["module"], r["name"]): r["reductionWitness"] for r in rows
                  if r["impliesAxiom"] == "Classical.choice" and r.get("requiredBehavior") and not r["matchingNameAndModule"]}
    for owner, name, operand, law, witness in checks:
        site = (owner, name)
        if site in sites or SPECIFIED_SELECTION.get(site) != (operand, law, witness) or reductions.get((owner, operand)) != witness:
            raise ValueError(f"invalid specified selector certificate for {site}")
        sites[site] = (operand, law)
    return sites
