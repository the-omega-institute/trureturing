using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementGeometry;

internal sealed class PrecisionSeparationPersistenceDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/RefinementGeometry/PrecisionSeparationPersistence."
            + "precision_separation_persists";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separation at one layer of a compatible precision tower persists at every finer layer.",
        H("Precision Separation Persistence"),
        Blocks(Describe.Lean(
            DescribeId.Create("precision-separation-persists"),
            DeclarationHandle.Create(Declaration),
            H("Separated states remain separated at every finer precision"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Each lowering map recovers the readout at its coarser layer exactly. "
                        + "Thus equality at a finer layer projects to equality at the "
                        + "preceding layer.")),
                Paragraph(Text(
                    "Induction across the interval from k to m transports any hypothetical "
                        + "equality back to layer k, contradicting the stated separation."))),
            DescribeRole.Theorem))));

    private static Formula Subscript(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula output = F.Id("O");
        Formula readout = F.Id("q");
        Formula lower = F.Id("rho");
        Formula level = F.Id("n");
        Formula coarse = F.Id("k");
        Formula fine = F.Id("m");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula next = Seq(level, Plus, D(1));
        Formula outputAtLevel = Subscript(output, level);
        Formula outputAtNext = Subscript(output, next);
        Formula readoutAtLevel = Subscript(readout, level);
        Formula readoutAtNext = Subscript(readout, next);
        Formula lowerAtLevel = Subscript(lower, level);

        Formula Read(Formula index, Formula state) =>
            Apply(Subscript(readout, index), state);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, stateType, Colon, Sp, type, Comma, Sp,
                output, Colon, Sp, naturals, Sp, To, Sp, type, Comma),
            Seq(
                readout, Colon, Sp, Forall, Sp, level, Colon, Sp, naturals,
                Comma, Sp, stateType, Sp, To, Sp, outputAtLevel, Comma),
            Seq(
                lower, Colon, Sp, Forall, Sp, level, Colon, Sp, naturals,
                Comma, Sp, outputAtNext, Sp, To, Sp, outputAtLevel, Comma),
            Seq(
                coarse, Comma, Sp, fine, Colon, Sp, naturals, Comma, Sp,
                left, Comma, Sp, right, Colon, Sp, stateType, Comma),
            Seq(
                Open, Forall, Sp, level, Colon, Sp, naturals, Comma, Sp,
                readoutAtLevel, Sp, Eq, Sp, lowerAtLevel, Sp, Circ, Sp,
                readoutAtNext, Close, Sp, Land, Sp,
                coarse, Sp, Leq, Sp, fine, Sp, Land),
            Seq(
                Read(coarse, left), Sp, Neq, Sp, Read(coarse, right),
                Sp, Rightarrow, Sp,
                Read(fine, left), Sp, Neq, Sp, Read(fine, right), Dot),
        ]));
    }
}
