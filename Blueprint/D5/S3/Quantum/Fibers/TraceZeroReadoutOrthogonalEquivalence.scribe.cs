using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class TraceZeroReadoutOrthogonalEquivalenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real trace-zero Hermitian readout fibers equal residual and projection fibers.",
        H("Trace-Zero Hermitian Readout Fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("trace-zero-hermitian-readout-residual-projection-equivalence"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Fibers/TraceZeroReadoutOrthogonalEquivalence."
                        + "readout_fiber_orthogonal_equivalence"),
                H("Trace readout fibers are residual and projection fibers on the real carrier"),
                StatementSource.FromAuthor(TraceZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The public carrier is the real subspace HermitianTraceZero(d) of "
                            + "complex d by d matrices that are Hermitian and trace zero. "
                            + "Raw effects and density matrices retain their source positivity "
                            + "and trace-one predicates; centered effects and centered states "
                            + "are constructed in this carrier.")),
                    Paragraph(Text(
                        "Let V_0 be the real span of the centered effects and R_0 its "
                            + "orthogonal complement in HermitianTraceZero(d). Equality of the "
                            + "finite trace readouts is equivalent to every trace pairing being "
                            + "zero, to the centered-state difference lying in R_0, and to equal "
                            + "orthogonal projections onto V_0.")),
                    Paragraph(Text(
                        "The frozen finite expectation-word residual theorem is applied on the "
                            + "real subtype. Matrix trace and complex-inner-product identities "
                            + "bridge its real pairing to the source's complex trace equation."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TraceZeroFormula()
    {
        Formula d = F.Id("d");
        Formula m = F.Id("m");
        Formula effect = F.Id("E");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula matrix = Call("Matrix", d, d, complex);
        Formula carrier = F.Id("V");
        Formula carrierType = Call("HermitianTraceZero", d);
        Formula readoutRho = Call("finiteTraceReadout", effect, Rho);
        Formula readoutSigma = Call("finiteTraceReadout", effect, SigmaLower);
        Formula indexedEffect = Seq(effect, Open, F.Id("i"), Close);
        Formula tracePairing = Seq(
            Call("Tr", Seq(Open, Rho, Minus, SigmaLower, Close, indexedEffect)),
            Sp, Eq, Sp, D(0));
        Formula xRho = Seq(F.Id("X"), Underscore, Rho);
        Formula xSigma = Seq(F.Id("X"), Underscore, SigmaLower);
        Formula difference = Seq(xRho, Sp, Minus, Sp, xSigma);
        Formula visible = Seq(
            Operatorname, Grp(F.Id("span")), Underscore, Grp(real), Open,
            Operatorname, Grp(F.Id("range")), Open,
            Call("centeredEffect", indexedEffect), Close, Close);
        Formula residual = Seq(F.Id("R"), Underscore, Grp(D(0)));
        Formula projection = Seq(F.Id("P"), Underscore, Grp(
            Seq(F.Id("V"), Underscore, Grp(D(0)))));
        Formula projectionRho = Seq(projection, Open, xRho, Close);
        Formula projectionSigma = Seq(projection, Open, xSigma, Close);
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula fin = Seq(Operatorname, Grp(F.Id("Fin")), Open,
            Seq(m, Plus, D(1)), Close);
        Formula effectType = new Formula.TypeArrow(fin, matrix);
        Formula stateHypothesis = Seq(
            Rho, Sp, Operatorname, Grp(F.Id("PosSemidef")), Sp, Land, Sp,
            Call("trace", Rho), Sp, Eq, Sp, D(1));
        Formula sigmaHypothesis = Seq(
            SigmaLower, Sp, Operatorname, Grp(F.Id("PosSemidef")), Sp, Land, Sp,
            Call("trace", SigmaLower), Sp, Eq, Sp, D(1));
        Formula effectHypothesis = Seq(
            Forall, Sp, F.Id("i"), Colon, Sp, fin, Comma, Sp,
            Open, indexedEffect, Sp, Operatorname, Grp(F.Id("PosSemidef")), Sp,
            Land, Sp, Open, D(1), Sp, Minus, Sp, indexedEffect, Close, Sp,
            Operatorname, Grp(F.Id("PosSemidef")), Close);

        return Disp(Seq(
            Forall, Sp, d, Colon, Sp, type, Comma, Sp, m, Colon, Sp, F.Id("Nat"),
            Comma, Sp, OpenBracket, Call("Fintype", d), CloseBracket, Comma, Sp,
            OpenBracket, Call("Nonempty", d), CloseBracket, Comma, Sp,
            OpenBracket, Call("DecidableEq", d), CloseBracket, RowBreak, Grp(),
            effect, Colon, Sp, effectType, Comma, Sp,
            Rho, Comma, Sp, SigmaLower, Colon, Sp, matrix, Comma, Sp,
            stateHypothesis, Comma, Sp, sigmaHypothesis, Comma, RowBreak, Grp(),
            effectHypothesis, Sp, Rightarrow, RowBreak, Grp(),
            carrier, Sp, Eq, Sp, carrierType, Comma, Sp,
            Call("V0", carrier, effect), Sp, Eq, Sp, visible, Comma, Sp,
            Call("R0", carrier, effect), Sp, Eq, Sp,
            Seq(F.Id("V0"), Caret, Grp(Perp)), Comma, RowBreak, Grp(),
            Open,
            Open, readoutRho, Eq, readoutSigma, Close, Sp, Leftrightarrow, Sp,
            Open, Forall, Sp, F.Id("i"), Comma, Sp, tracePairing, Close,
            Close, Sp, Land, RowBreak, Grp(),
            Open,
            Open, Forall, Sp, F.Id("i"), Comma, Sp, tracePairing, Close,
            Sp, Leftrightarrow, Sp, Open, difference, Sp, InMacro, Sp, residual, Close,
            Close, Sp, Land, RowBreak, Grp(),
            Open,
            Open, difference, Sp, InMacro, Sp, residual, Close, Sp, Leftrightarrow, Sp,
            Open, projectionRho, Eq, projectionSigma, Close,
            Close, Dot));
    }
}
