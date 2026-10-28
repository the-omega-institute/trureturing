using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class CountableSignedMeasureReflectionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/CountableSignedMeasureReflection.";
    private static Formula Id(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula At(string family, Formula n) => Call(family, n);
    private static Formula Mass(string part, Formula s) => Call("mass", Call(part, s), Id("univ"));
    private static Formula Preserves(Formula s, Formula p) => And(
        Eq(Mass("totalVariation", Call("map", s, p)), Mass("totalVariation", s)),
        And(Eq(Mass("posPart", Call("map", s, p)), Mass("posPart", s)),
            Eq(Mass("negPart", Call("map", s, p)), Mass("negPart", s))));
    private static Formula Statement()
    {
        Formula i = Id("i"), j = Id("j"), n = Id("n"), beta = Id("beta"), gamma = Id("gamma");
        Formula stage = Id("CountableStage"), index = Id("I");
        Formula p(Formula b) => Call("projection", Id("C"), b);
        Formula trace(Formula k) => Call("preimage", p(beta), At("V", k));
        Formula later = All("gamma", stage, Imp(Call("Le", beta, gamma), All("n", Id("Nat"),
            And(Preserves(At("s", n), p(gamma)), Eq(Call("totalVariation", Call("map", At("s", n), p(gamma))),
                Call("measureMap", Call("totalVariation", At("s", n)), p(gamma)))))));
        Formula nullity = All("n", Id("Nat"), All("i", index, Iff(
            Eq(Call("mass", Call("totalVariation", Call("map", At("s", n), p(beta))), Call("compl", At("V", i))), Id("zero")),
            Eq(Call("mass", Call("totalVariation", At("s", n)), Call("compl", At("W", i))), Id("zero")))));
        Formula clopen = All("i", index, Call("IsClopen", At("V", i)));
        Formula traces = All("i", index, Eq(At("W", i), trace(i)));
        Formula nonempty = All("i", index,
            Iff(Call("Nonempty", At("V", i)), Call("Nonempty", At("W", i))));
        Formula disjoint = All("i", index, All("j", index,
            Iff(Call("Disjoint", At("V", i), At("V", j)),
                Call("Disjoint", At("W", i), At("W", j)))));
        Formula result = Ex("beta", stage, And(Call("Le", Id("base"), beta),
            Ex("V", Call("Family", index, Call("Set", Call("Fobj", Call("op", beta)))),
                And(clopen, And(traces, And(nonempty, And(disjoint, And(later, nullity))))))));
        Formula body = All("W", Call("Family", index, Call("Set", Call("Cpt", Id("C")))),
            Imp(All("i", index, Call("IsClopen", At("W", i))), result));
        body = All("s", Call("Family", Id("Nat"), Call("SignedMeasure", Call("Cpt", Id("C")))),
            Imp(All("n", Id("Nat"), Call("Regular", Call("totalVariation", At("s", n)))), body));
        body = All("base", stage, body);
        body = Imp(Call("SurjectiveBonding", Id("F")), body);
        body = All("C", Call("Cone", Id("F")), Imp(Call("BorelLimitCone", Id("C")), body));
        body = All("F", Call("Functor", Id("CountableStageOpp"), Id("Profinite1")),
            Imp(Call("NonemptyBorelComponents", Id("F")), body));
        return Disp(All("I", Id("TypeW"), Imp(Call("Countable", index), body)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One proper stage preserves the whole countable signed family's total variation and Jordan masses and reflects the supplied clopens.",
        H("Exact countable signed norm reflection"),
        Blocks(
            Paragraph(Text(
                "CountableStage is the actual subtype of ordinals strictly below omega-one. F is a Profinite diagram on its opposite category, with nonempty carriers, Borel measurable structures and surjective bonding maps. "
                + "C is the actual limit cone with its Borel measurable structure. NonemptyBorelComponents abbreviates exactly these component hypotheses; BorelLimitCone includes the IsLimit witness and Borel structure of the cone point. "
                + "In the formula mass is measure application, posPart and negPart are the actual Jordan parts, map is signed pushforward and measureMap is positive-measure pushforward. Profinite1 fixes universe one and CountableStageOpp is the opposite stage category. "
                + "s is any natural-indexed family of actual finite real signed measures with regular total variation. I is any countable type, including the empty type, and W is any I-indexed clopen family.")),
            Describe.Lean(
                DescribeId.Create("exists-common-stage"), DeclarationHandle.Create(Owner + "exists_common_stage"),
                H("One common proper stage with exact signed masses"), StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/kania2026talagrand")),
                Blocks(
                    Paragraph(Text(
                        "There is beta at or above the prescribed base, still strictly below omega-one. Each W(i) is the full inverse image of a clopen V(i) under the actual beta projection. "
                        + "Nonemptiness and all pairwise disjointness relations are equivalent at the final and beta levels. For every later proper gamma with beta <= gamma and every n, the pushed signed measure has exactly the original total variation, positive Jordan and negative Jordan whole masses. "
                        + "These masses are in extended nonnegative real units, not a normalized replacement. Its variation measure equals the pushforward of the original variation. At beta, variation-nullity of the complement of V(i) is equivalent to original variation-nullity of the complement of W(i), for every n and i.")),
                    Paragraph(Text(
                        "RegularSignedLift.regular_jordanParts_of_regular_totalVariation supplies regularity of both original Jordan parts. PositiveClopenMass.exists_isClopen_subset_lt_apply_of_lt_posPart gives A(n,k) with signed mass greater than the positive whole mass minus 1/(k+1), including zero positive mass. "
                        + "CountableClopenReflection.exists_common_stage reflects the disjoint union of the entire witness family and W at one beta. Signed evaluation on every witness is unchanged. Each evaluation is bounded by the pushed positive whole mass. "
                        + "Variation contraction and preservation of total signed mass imply the opposite upper bound on the pushed positive mass, using twice positive mass = variation mass + signed mass. Archimedean squeezing forces equality. Jordan subtraction then gives negative-mass equality and addition gives variation-mass equality. "
                        + "No regularity of the pushed Jordan parts is used in this squeeze, and no projection is assumed isometric.")),
                    Paragraph(Text(
                        "For beta <= gamma, cone naturality identifies projection to beta with projection to gamma followed by its bonding map. Positive-mass contraction for the two maps sandwiches the mass at gamma between equal endpoint masses. "
                        + "NormPreservingLifts.totalVariation_map_of_mass upgrades equality of whole variation mass to equality of the variation measures. Evaluation of this equality on clopen complements proves the stated support-nullity equivalence.")),
                    Paragraph(Text(
                        "Application to SignedBirthEnumeration.BornData uses I = Nat and a supplied disjoint nonempty clopen support family W. The reflected V is a SupportFamily by the two exact equivalences. "
                        + "If each original signed measure has variation whole mass one, positive Jordan whole mass at least one half and zero variation outside W(n), the pushed whole sequence has those same three properties. "
                        + "Continuous pushforward of the original regular finite variation is regular; the proved variation-measure identity and RegularSignedLift recover regular Jordan parts at beta. Hence this is legal whole BornData at that one beta. "
                        + "On a live CH path, exists_signed_enumeration chooses one label for this entire BornData value at the actual launch row; labels are not chosen separately for individual terms. No CH hypothesis is needed for reflection itself. "
                        + "This supplier neither constructs the transfinite compactum nor provides a full raw history, final collision or a solution to the CH signed Talagrand problem."))),
                DescribeRole.Theorem))));
}
