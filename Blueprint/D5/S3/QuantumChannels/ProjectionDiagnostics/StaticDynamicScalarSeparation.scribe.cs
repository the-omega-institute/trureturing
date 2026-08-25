using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels.ProjectionDiagnostics;

internal sealed class StaticDynamicScalarSeparationDocument : IScribeDocumentDefinition
{
    private const string DeclarationRoot =
        "D5/S3/QuantumChannels/ProjectionDiagnostics/StaticDynamicScalarSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unread-measurement coherence loss and residual-to-visible generator return are "
            + "independent quantitative diagnostics.",
        H("Static and Dynamic Projection Diagnostics Are Independent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pinching-as-a-linear-endomorphism"),
                DeclarationHandle.Create(DeclarationRoot + "pinchingEnd"),
                H("Pinching is packaged as a linear endomorphism"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, Rho, Colon, Sp, F.Id("QubitMatrix"), Comma, Sp,
                    Call("pinchingEnd", Rho), Sp, Eq, Sp, Call("pinching", Rho), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The endomorphism applies the repository's standard-basis pinching channel. "
                        + "Its linear laws follow entrywise from the existing channel formula."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("upper-residual-return-generator"),
                DeclarationHandle.Create(DeclarationRoot + "residualReturnGenerator"),
                H("The generator returns one residual coordinate to the visible diagonal"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("A"), Colon, Sp, F.Id("QubitMatrix"), Comma, Sp,
                    F.Id("i"), Comma, Sp, F.Id("j"), Colon, Sp, Call("Fin", D(2)), Comma, Sp,
                    Call("residualReturnGenerator", F.Id("A"), F.Id("i"), F.Id("j")),
                    Sp, Eq, Sp,
                    Sub(F.Id("A"), Seq(D(0), D(1))), Comma, Sp,
                    Operatorname, Grp(F.Id("if")), Sp,
                    Open, F.Id("i"), Comma, F.Id("j"), Close, Eq,
                    Open, D(0), Comma, D(0), Close, Semi, Sp,
                    D(0), Comma, Sp, Operatorname, Grp(F.Id("otherwise")),
                    Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This explicit complex-linear generator reads the upper off-diagonal entry "
                        + "and writes it into the first diagonal entry. It therefore transports "
                        + "a discarded residual coordinate back into the visible block."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("static-loss-and-dynamic-return-are-independent"),
                DeclarationHandle.Create(
                    DeclarationRoot + "static_loss_and_dynamic_return_are_independent"),
                H("Static coherence loss and dynamic return vary independently"),
                StatementSource.FromAuthor(IndependenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real lower bound, scaling a single off-diagonal matrix entry "
                            + "makes the Hilbert--Schmidt mass discarded by pinching exceed that "
                            + "bound. The identity generator still has zero residual-to-visible "
                            + "block because pinching is idempotent.")),
                    Paragraph(Text(
                        "For every positive real upper bound, a smaller positive off-diagonal "
                            + "entry gives discarded mass strictly between zero and that bound. "
                            + "The explicit residual-return generator nevertheless has a nonzero "
                            + "visible return block. Both contrast clauses use the same pinching "
                            + "channel on the complex qubit-matrix carrier."))),
                DescribeRole.Theorem))));

    private static Formula StaticLoss(Formula rho)
    {
        Formula residual = Seq(Open, rho, Sp, Minus, Sp, Call("pinching", rho), Close);
        return Seq(Re, Sp, Call("hilbertSchmidtInner", residual, residual));
    }

    private static Formula IdentityReturnBlock() =>
        Seq(
            F.Id("pinchingEnd"), Sp, Circ, Sp, F.Id("I"), Sp, Circ, Sp,
            Open, F.Id("I"), Sp, Minus, Sp, F.Id("pinchingEnd"), Close);

    private static Formula ActiveReturnBlock() =>
        Seq(
            F.Id("pinchingEnd"), Sp, Circ, Sp, F.Id("residualReturnGenerator"),
            Sp, Circ, Sp, Open, F.Id("I"), Sp, Minus, Sp, F.Id("pinchingEnd"), Close);

    private static Formula Sub(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula IndependenceFormula()
    {
        Formula rho = Rho;
        Formula qubitMatrix = F.Id("QubitMatrix");
        Formula lower = F.Id("lower");
        Formula upper = F.Id("upper");

        return Disp(Seq(
            OpenBracket,
            Forall, Sp, lower, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            Exists, Sp, rho, InMacro, Sp, qubitMatrix, Comma, Sp,
            lower, Sp, Lt, Sp, StaticLoss(rho), Sp, Land, Sp,
            IdentityReturnBlock(), Sp, Eq, Sp, D(0),
            CloseBracket,
            Sp, Land, Sp,
            OpenBracket,
            Forall, Sp, upper, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            D(0), Sp, Lt, Sp, upper, Sp, Rightarrow, Sp,
            Exists, Sp, rho, InMacro, Sp, qubitMatrix, Comma, Sp,
            D(0), Sp, Lt, Sp, StaticLoss(rho), Sp, Land, Sp,
            StaticLoss(rho), Sp, Lt, Sp, upper, Sp, Land, Sp,
            ActiveReturnBlock(), Sp, Neq, Sp, D(0),
            CloseBracket, Dot));
    }
}
