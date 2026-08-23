using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class ReadoutOrthogonalEquivalenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite trace readout fibers are centered-effect residual and projection fibers.",
        H("Trace Readout Fibers and Orthogonal Residuals"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("trace-readout-fiber-is-centered-orthogonal-residual"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Fibers/ReadoutOrthogonalEquivalence."
                        + "readout_fiber_orthogonal_equivalence"),
                H("Trace readout equality is orthogonal residual equality"),
                StatementSource.FromAuthor(ReadoutResidualFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state and effect objects are finite complex matrices. Density "
                            + "matrices are positive semidefinite and trace one, and every "
                            + "accessible effect and its complement are positive semidefinite. "
                            + "The readout is constructed from trace expectations.")),
                    Paragraph(Text(
                        "Centering removes the scalar identity components from states and "
                            + "effects. Equality of readouts is equivalent to vanishing of "
                            + "every trace pairing, then to membership in the orthogonal "
                            + "complement of the centered-effect span, and finally to equality "
                            + "of the visible orthogonal projections.")),
                    Paragraph(Text(
                        "The residual and projection equivalences are supplied directly by the "
                            + "canonical finite expectation-word theorem. Pinned library trace "
                            + "and matrix-inner-product declarations bridge that theorem to the "
                            + "source trace readout."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula ReadoutResidualFormula()
    {
        Formula n = F.Id("n");
        Formula m = F.Id("m");
        Formula effect = F.Id("E");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = Call("Matrix", n, n, complex);
        Formula readout = Seq(F.Id("q"), Underscore, Grp(effect));
        Formula readoutRho = Seq(readout, Open, Rho, Close);
        Formula readoutSigma = Seq(readout, Open, SigmaLower, Close);
        Formula indexedEffect = Seq(effect, Underscore, Grp(F.Id("i")));
        Formula tracePairing = Seq(
            Operatorname, Grp(F.Id("Tr")), Open,
            Open, Rho, Minus, SigmaLower, Close, indexedEffect, Close, Eq, D(0));
        Formula difference = Seq(
            F.Id("X"), Underscore, Rho, Minus,
            F.Id("X"), Underscore, SigmaLower);
        Formula residual = Seq(F.Id("R"), Underscore, Grp(D(0)));
        Formula visible = Seq(F.Id("V"), Underscore, Grp(D(0)));
        Formula projection = Seq(F.Id("P"), Underscore, Grp(visible));
        Formula projectionRho = Seq(
            projection, Open, F.Id("X"), Underscore, Rho, Close);
        Formula projectionSigma = Seq(
            projection, Open, F.Id("X"), Underscore, SigmaLower, Close);

        return Disp(Seq(
            Forall, Sp, n, Comma, Sp, m, Comma, Sp,
            effect, Colon, Sp, Operatorname, Grp(F.Id("Fin")), Open,
            m, Plus, D(1), Close, To, matrix, Comma, Sp,
            Rho, Comma, Sp, SigmaLower, Colon, Sp, matrix, Comma, Sp,
            Call("Density", Rho), Land, Call("Density", SigmaLower), Land,
            Call("EffectFamily", effect), Sp, Rightarrow, RowBreak,
            Open,
            Open, readoutRho, Eq, readoutSigma, Close, Leftrightarrow,
            Open, Forall, Sp, F.Id("i"), Comma, Sp, tracePairing, Close,
            Close, Land, RowBreak,
            Open,
            Open, Forall, Sp, F.Id("i"), Comma, Sp, tracePairing, Close,
            Leftrightarrow, Open, difference, InMacro, Sp, residual, Close,
            Close, Land, RowBreak,
            Open,
            Open, difference, InMacro, Sp, residual, Close, Leftrightarrow,
            Open, projectionRho, Eq, projectionSigma, Close,
            Close, Dot));
    }
}
