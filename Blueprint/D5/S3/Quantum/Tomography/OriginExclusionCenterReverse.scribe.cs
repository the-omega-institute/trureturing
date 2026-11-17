using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class OriginExclusionCenterReverseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The common effect that separates two pure points orders the centres of their complete exclusion balls in the reverse direction.",
        H("Strict reverse ordering of exclusion-ball centres"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strict-reverse-ordering-of-exclusion-ball-centres"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/OriginExclusionCenterReverse."
                        + "strict_centre_reverse"),
                H("Weak centre bounds and strict reverse ordering"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The structure SeparationData records two complete exclusion balls, "
                            + "their centres, two pure points, the two reflected points, one "
                            + "linear effect, and the endpoint and uniqueness conditions used "
                            + "by the source argument.")),
                    Paragraph(Text(
                        "The reflection identities are r = 2 c_p - q and s = 2 c_q - p. "
                            + "Applying the global effect bounds to these points gives "
                            + "f(c_p) at most one half and one half at most f(c_q).")),
                    Paragraph(Text(
                        "If equality held between the centre values, both would be one half "
                            + "and the first reflected point would attain value one. Its "
                            + "membership in the second complete ball and the unique-maximizer "
                            + "hypothesis would identify it with the pure point excluded from "
                            + "the first ball, contradicting its recorded membership there. "
                            + "Thus the weak bounds sharpen to the strict inequality.")),
                    Paragraph(Text(
                        "This module isolates the reflection and unique-maximum algebraic core. "
                            + "It does not encode the finite-dimensional convex classification "
                            + "or claim a physical realization."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula TheoremFormula()
    {
        Formula data = Apply("SeparationData", F.Id("d"));
        Formula conclusion = And(
            new Formula.Relation(
                Apply("CentreEffect", F.Id("d"), F.Id("cp")),
                FormulaRelationOperator.LessThanOrEqual,
                new Formula.Fraction(D(1), D(2))),
            And(
                new Formula.Relation(
                    new Formula.Fraction(D(1), D(2)),
                    FormulaRelationOperator.LessThanOrEqual,
                    Apply("CentreEffect", F.Id("d"), F.Id("cq"))),
                new Formula.Relation(
                    Apply("CentreEffect", F.Id("d"), F.Id("cp")),
                    FormulaRelationOperator.LessThan,
                    Apply("CentreEffect", F.Id("d"), F.Id("cq")))));
        return Disp(Seq(
            data, Sp, Rightarrow, RowBreak,
            conclusion, Dot));
    }
}
