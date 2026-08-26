using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class OperationalReadoutQuotientRepresentationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula d = F.Id("d");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula system = F.Id("S");
        Formula readout = new Formula.Subscript(F.Id("r"), system);
        Formula quotientEquiv = new Formula.Subscript(F.Id("E"), system);
        Formula rho = Rho;
        Formula sigma = Sigma;
        Formula t = F.Id("t");
        Formula candidate = F.Id("EPrime");
        Formula stateType = Call("DensityState", d);
        Formula readoutType = Call("operatorSystemReadout", system);
        Formula quotientType = Call("Quotient", Call("ker", readout));
        Formula rangeType = Call("range", readout);
        Formula equivalenceType = Seq(quotientType, Sp, Equiv, Sp, rangeType);
        Formula stateClass(Formula state) => Call("class", state);
        Formula rangePoint(Formula state) => Call("rangePoint", Apply(readout, state));
        Formula computes(Formula equivalence, Formula state) =>
            Seq(Apply(equivalence, stateClass(state)), Sp, Eq, Sp, rangePoint(state));
        Formula mixture = new Formula.Subscript(Seq(Rho), Seq(t));
        Formula mixtureValue = Seq(
            t, Sp, Cdot, Sp, Call("matrix", rho), Sp, Plus, Sp,
            Grp(Seq(D(1), Sp, Minus, Sp, t)), Sp, Cdot, Sp,
            Call("matrix", sigma));
        Formula affineValue = Seq(
            t, Sp, Cdot, Sp,
            Call("value", Apply(quotientEquiv, stateClass(rho))), Sp, Plus, Sp,
            Grp(Seq(D(1), Sp, Minus, Sp, t)), Sp, Cdot, Sp,
            Call("value", Apply(quotientEquiv, stateClass(sigma))));
        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(d, type), Comma, Sp,
            Call("Fintype", d), Sp, Land, Sp, Call("DecidableEq", d), Sp,
            Rightarrow, RowBreak, Grp(),
            Forall, Sp, Typed(system, Call("MatrixOperatorSystem", d)), Comma,
            RowBreak, Grp(),
            readout, Sp, Colon, Eq, Sp, readoutType, Comma, Sp,
            quotientEquiv, Sp, Colon, Eq, Sp,
            Call("quotientKerEquivRange", readout), Colon, Sp, equivalenceType,
            Comma, RowBreak, Grp(),
            Grp(Seq(
                Forall, Sp, Typed(rho, stateType), Comma, Sp,
                computes(quotientEquiv, rho))), Sp, Land, RowBreak, Grp(),
            Grp(Seq(
                Forall, Sp, Typed(candidate, equivalenceType), Comma, Sp,
                Grp(Seq(
                    Forall, Sp, Typed(rho, stateType), Comma, Sp,
                    computes(candidate, rho))), Sp, Rightarrow, Sp,
                candidate, Sp, Eq, Sp, quotientEquiv)), Sp, Land, RowBreak, Grp(),
            Forall, Sp, Typed(t, real), Comma, Sp, Typed(rho, stateType), Comma, Sp,
            Typed(sigma, stateType), Comma, Sp,
            D(0), Sp, Leq, Sp, t, Sp, Leq, Sp, D(1), Sp, Rightarrow,
            RowBreak, Grp(),
            Exists, Sp, Bang, Sp, Typed(mixture, stateType), Comma, Sp,
            Call("matrix", mixture), Sp, Eq, Sp, mixtureValue, Sp, Land,
            RowBreak, Grp(),
            Call("value", Apply(quotientEquiv, stateClass(mixture))), Sp, Eq, Sp,
            affineValue, Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Operational state classes are canonically and affinely represented by realized readouts.",
            H("Operational Readout Quotient Representation"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("operational-readout-quotient-is-its-affine-range"),
                    DeclarationHandle.Create(
                        "D5/S3/Quantum/Completion/OperationalReadoutQuotientRepresentation."
                            + "operational_readout_quotient_representation"),
                    H("The operational quotient is canonically its readout range"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Density states are identified exactly when every effect in the "
                                + "chosen operator system has the same trace expectation.")),
                        Paragraph(Text(
                            "The named kernel-range equivalence sends each state class to its "
                                + "realized readout and is uniquely determined by this rule.")),
                        Paragraph(Text(
                            "Positive trace-one matrices are closed under binary mixtures. "
                                + "Trace linearity then shows that the canonical equivalence "
                                + "preserves every such convex combination pointwise."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

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
}
