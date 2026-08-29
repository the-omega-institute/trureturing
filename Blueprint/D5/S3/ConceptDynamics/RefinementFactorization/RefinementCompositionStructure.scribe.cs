using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementFactorization;

internal sealed class RefinementCompositionStructureDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/RefinementFactorization/RefinementCompositionStructure."
            + "refinement_composition_category_and_quotient_preorder";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refinement composes, forms a factorization category, and descends to a preorder.",
        H("Refinement Composition Structure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refinement-composition-category-preorder"),
                DeclarationHandle.Create(Declaration),
                H("Refinement composition, category laws, and quotient preorder"),
                StatementSource.FromAuthor(CompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Canonical refinement is factorization of one concept readout through "
                            + "another. Existing family theorems supply transitivity by "
                            + "composition and reflexivity by the identity map.")),
                    Paragraph(Text(
                        "The named factorization-category object uses those source maps as its "
                            + "morphisms. The public statement exposes its identity and "
                            + "composition computations together with both unit laws and "
                            + "associativity.")),
                    Paragraph(Text(
                        "All bundled concept readouts are quotiented by mutual refinement "
                            + "through Mathlib antisymmetrization. The quotient order is "
                            + "identified publicly with refinement of representatives and is "
                            + "then stated directly to be reflexive and transitive."))),
                DescribeRole.Theorem))));

    private static Formula Refines(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula CompositionFormula()
    {
        Formula state = F.Id("X");
        Formula coarseType = F.Id("BC");
        Formula middleType = F.Id("BD");
        Formula fineType = F.Id("BE");
        Formula coarse = F.Id("C");
        Formula middle = F.Id("D");
        Formula fine = F.Id("E");
        Formula readout = F.Id("r");
        Formula firstReadout = F.Id("r0");
        Formula secondReadout = F.Id("r1");
        Formula thirdReadout = F.Id("r2");
        Formula fourthReadout = F.Id("r3");
        Formula firstFactor = F.Id("h0");
        Formula secondFactor = F.Id("h1");
        Formula thirdFactor = F.Id("h2");
        Formula factor = F.Id("h");
        Formula firstClass = F.Id("A");
        Formula secondClass = F.Id("B");
        Formula leftClass = F.Id("left");
        Formula middleClass = F.Id("middle");
        Formula rightClass = F.Id("right");
        Formula relationLeft = F.Id("P");
        Formula relationRight = F.Id("Q");
        Formula classType = Call("ReadoutRefinementClass", state);
        Formula readoutType = Call("Readout", state);
        Formula category = Call("fixedCodomainFactorizationCategory", state);
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula composition = Seq(
            Refines(coarse, middle), Sp, Rightarrow, Sp,
            Refines(middle, fine), Sp, Rightarrow, Sp,
            Refines(coarse, fine));
        Formula identityComputation = Seq(
            Forall, Sp, readout, Colon, Sp, readoutType, Comma, Sp,
            Call("identity", category, readout), Sp, Eq, Sp,
            Call("identityRefinement", Call("readout", readout)));
        Formula compositionComputation = Seq(
            Forall, Sp, firstReadout, Comma, Sp, secondReadout, Comma, Sp,
            thirdReadout, Colon, Sp, readoutType, Comma, Sp,
            firstFactor, Colon, Sp,
            Refines(Call("readout", firstReadout), Call("readout", secondReadout)),
            Comma, Sp,
            secondFactor, Colon, Sp,
            Refines(Call("readout", secondReadout), Call("readout", thirdReadout)),
            Comma, Sp,
            Call("compose", category, firstFactor, secondFactor), Sp, Eq, Sp,
            Call("composeRefinement", secondFactor, firstFactor));
        Formula leftIdentity = Seq(
            Forall, Sp, firstReadout, Comma, Sp, secondReadout,
            Colon, Sp, readoutType, Comma, Sp,
            factor, Colon, Sp,
            Refines(Call("readout", firstReadout), Call("readout", secondReadout)),
            Comma, Sp,
            Call("compose", category, Call("identity", category, firstReadout), factor),
            Sp, Eq, Sp, factor);
        Formula rightIdentity = Seq(
            Forall, Sp, firstReadout, Comma, Sp, secondReadout,
            Colon, Sp, readoutType, Comma, Sp,
            factor, Colon, Sp,
            Refines(Call("readout", firstReadout), Call("readout", secondReadout)),
            Comma, Sp,
            Call("compose", category, factor, Call("identity", category, secondReadout)),
            Sp, Eq, Sp, factor);
        Formula associativity = Seq(
            Forall, Sp, firstReadout, Comma, Sp, secondReadout, Comma, Sp,
            thirdReadout, Comma, Sp, fourthReadout, Colon, Sp, readoutType, Comma, Sp,
            firstFactor, Colon, Sp,
            Refines(Call("readout", firstReadout), Call("readout", secondReadout)),
            Comma, Sp,
            secondFactor, Colon, Sp,
            Refines(Call("readout", secondReadout), Call("readout", thirdReadout)),
            Comma, Sp,
            thirdFactor, Colon, Sp,
            Refines(Call("readout", thirdReadout), Call("readout", fourthReadout)),
            Comma, Sp,
            Call(
                "compose", category,
                Call("compose", category, firstFactor, secondFactor), thirdFactor),
            Sp, Eq, Sp,
            Call(
                "compose", category, firstFactor,
                Call("compose", category, secondFactor, thirdFactor)));
        Formula readoutRelation = Seq(
            Open, relationLeft, Comma, Sp, relationRight, Colon, Sp, readoutType,
            Sp, Mapsto, Sp, relationLeft, Sp, Leq, Sp, relationRight, Close);
        Formula quotientOrder = Seq(
            Forall, Sp, firstClass, Comma, Sp, secondClass,
            Colon, Sp, readoutType, Comma, Sp,
            Call("toAntisymmetrization", readoutRelation, firstClass),
            Sp, Leq, Sp,
            Call("toAntisymmetrization", readoutRelation, secondClass),
            Sp, Iff, Sp,
            Refines(Call("readout", firstClass), Call("readout", secondClass)));
        Formula quotientReflexive = Seq(
            Forall, Sp, leftClass, Colon, Sp, classType, Comma, Sp,
            leftClass, Sp, Leq, Sp, leftClass);
        Formula quotientTransitive = Seq(
            Forall, Sp, leftClass, Comma, Sp, middleClass, Comma, Sp, rightClass,
            Colon, Sp, classType, Comma, Sp,
            leftClass, Sp, Leq, Sp, middleClass, Sp, Rightarrow, Sp,
            middleClass, Sp, Leq, Sp, rightClass, Sp, Rightarrow, Sp,
            leftClass, Sp, Leq, Sp, rightClass);
        Formula categoryLaws = Seq(
            Open,
            Open, identityComputation, Close, Sp, Land, RowBreak, Grp(),
            Open, compositionComputation, Close, Sp, Land, RowBreak, Grp(),
            Open, leftIdentity, Close, Sp, Land, RowBreak, Grp(),
            Open, rightIdentity, Close, Sp, Land, RowBreak, Grp(),
            Open, associativity, Close,
            Close);
        Formula quotientLaws = Seq(
            Open,
            Open, quotientOrder, Close, Sp, Land, RowBreak, Grp(),
            Open, quotientReflexive, Close, Sp, Land, RowBreak, Grp(),
            Open, quotientTransitive, Close,
            Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            state, Comma, Sp, coarseType, Comma, Sp, middleType, Comma, Sp, fineType,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            coarse, Colon, Sp, Call("Concept", state, coarseType), Comma, Sp,
            middle, Colon, Sp, Call("Concept", state, middleType), Comma, Sp,
            fine, Colon, Sp, Call("Concept", state, fineType), Comma, RowBreak, Grp(),
            Open, composition, Close, Sp, Land, RowBreak, Grp(),
            Refines(coarse, coarse), Sp, Land, RowBreak, Grp(),
            categoryLaws, Sp, Land, RowBreak, Grp(),
            quotientLaws, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
