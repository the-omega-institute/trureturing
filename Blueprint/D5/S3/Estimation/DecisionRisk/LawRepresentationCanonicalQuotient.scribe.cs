using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class LawRepresentationCanonicalQuotientDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A law-determining representation refines the canonical law quotient.",
        H("Law Representations and the Canonical Quotient"),
        Blocks(Describe.Lean(
            DescribeId.Create(
                "law-determining-representation-refines-canonical-law-quotient"),
            DeclarationHandle.Create(
                "D5/S3/Estimation/DecisionRisk/LawRepresentationCanonicalQuotient."
                    + "law_determining_representation_refines_canonical_law_quotient"),
            H("Law-determining representations refine the canonical quotient"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The complete experiment law is an arbitrary typed map from State to Law. "
                        + "A representation determines it through the displayed decodeLaw "
                        + "factorization.")),
                Paragraph(Text(
                    "Equal representation values therefore give equal complete laws. The same "
                        + "law map defines the canonical equality-kernel quotient; its Mathlib "
                        + "kerLift is injective and reconstructs the law after the quotient "
                        + "projection.")),
                Paragraph(Text(
                    "Thus the quotient retains exactly the state distinctions visible to the "
                        + "experiment law. No second law, quotient, or equivalence relation is "
                        + "introduced."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("State");
        Formula representationType = F.Id("Representation");
        Formula lawType = F.Id("Law");
        Formula law = F.Id("Lambda");
        Formula representation = F.Id("r");
        Formula decodeLaw = Phi;
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula kernel = Call("ker", law);
        Formula projection = Call("quotientProjection", kernel);
        Formula liftedLaw = Call("kerLift", law);
        Formula sameRepresentation = new Formula.Relation(
            Call("r", x), FormulaRelationOperator.Equal, Call("r", y));
        Formula sameLaw = new Formula.Relation(
            Call("Lambda", x), FormulaRelationOperator.Equal, Call("Lambda", y));
        Formula fiberRefinement = Seq(
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, state, Comma, Sp,
            sameRepresentation, Sp, Rightarrow, Sp, sameLaw);
        Formula canonicalLaw = new Formula.Relation(
            law,
            FormulaRelationOperator.Equal,
            Seq(liftedLaw, Sp, Circ, Sp, projection));

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, representationType, Comma, Sp,
            lawType, Colon, Sp, F.Id("Type"), Comma, RowBreak, Grp(),
            law, Colon, Sp, Arrow(state, lawType), Comma, Sp,
            representation, Colon, Sp, Arrow(state, representationType), Comma, RowBreak, Grp(),
            decodeLaw, Colon, Sp, Arrow(representationType, lawType), Comma, Sp,
            law, Sp, Eq, Sp, decodeLaw, Sp, Circ, Sp, representation,
            Sp, Rightarrow, RowBreak, Grp(),
            Open, fiberRefinement, Close, Sp, Land, RowBreak, Grp(),
            Call("Injective", liftedLaw), Sp, Land, Sp,
            canonicalLaw, Dot));
    }
}
