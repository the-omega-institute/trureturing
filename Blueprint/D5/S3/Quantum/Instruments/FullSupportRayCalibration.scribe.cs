using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Instruments;

internal sealed class FullSupportRayCalibrationDocument : IScribeDocumentDefinition
{
    private static Formula Call(string name, params Formula[] arguments) =>
        Seq(Mathrm, Grp(F.Id(name)), Open, Seq(arguments), Close);

    private static Formula Statement()
    {
        var i = F.Id("i");
        var index = F.Id("I");
        var basis = F.Id("b");
        var space = F.Id("V");
        var field = F.Id("K");
        var scalar = F.Id("c");
        var b = new Formula.Subscript(basis, i);
        var a = new Formula.Subscript(F.Id("a"), i);
        var T = F.Id("T");
        var J = F.Id("J");
        var u = F.Id("u");
        var support = Call("supp", u);
        var inputEquality = Seq(T, u, Eq, scalar, J, u);
        var basisEquality = Seq(Forall, Sp, i, InMacro, Sp, index, Comma, Sp, T, b, Eq, a, J, b);
        return Disp(Seq(
            Call("Field", field), Land, Sp, Call("Finite", index), Land, Sp, Call("Basis", basis, Comma, space),
            Land, Sp, T, Comma, J, InMacro, Sp, new Formula.Subscript(Call("Hom", space, Comma, F.Id("W")), field),
            Land, Sp, Call("Injective", J), Land, Sp, Open, basisEquality, Close, Sp, Rightarrow, Sp,
            Open, inputEquality, Iff, Sp, Forall, Sp, i, InMacro, Sp, support, Comma, Sp, a, Eq, scalar, Close,
            Sp, Land, Sp, Open, support, Eq, index, Rightarrow, Sp, Open, inputEquality, Iff, Sp, T, Eq, scalar, J,
            Close, Close));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A calibration on a basis and a single full-support input determines a branch coefficient map up to one scalar relative to an injective reference.",
        H("Support-sensitive calibration of a branch coefficient map"),
        Blocks(Describe.Lean(DescribeId.Create("support-calibration"),
            DeclarationHandle.Create("D5/S3/Quantum/Instruments/FullSupportRayCalibration.support_calibration"),
            H("Which diagonal coefficients an additional input identifies"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Let J be an injective linear reference map between vector spaces over a field. For a finite input basis, suppose T sends each basis vector to a scalar aᵢ times its J-image. The extra test T(u)=cJ(u) holds exactly when aᵢ=c at every nonzero coordinate of u. If all coordinates of u are nonzero, passing the test is equivalent to T=cJ on the whole input.")),
                Paragraph(Text("Expand u in the basis, push both linear maps through the finite sum, and cancel the injective J. The resulting coordinate equations are uᵢaᵢ=uᵢc. In the quantum application, J includes an outcome subspace in the output Hilbert space. Suppose the unnormalized positive branch output for each probe v is supported on the line spanned by Jv. For any w perpendicular to Jv, its quadratic form is the sum over Kraus operators A of the nonnegative numbers |⟨w,Av⟩|². This sum is zero, hence each Av belongs to the line spanned by Jv. Zero-probability Kraus contributions are included. Applying the algebraic theorem to each restricted A at the basis and the extra probe makes that A a scalar multiple of J."))), DescribeRole.Theorem))));
}
