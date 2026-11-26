using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk;

internal sealed class WalkDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/Walk.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Hamming/ide2026scaling");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The source CT matrix and complex DT evolution agree with their Walsh expansions.",
        H("The origin-started walks in Walsh coordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("continuousstate-fourier"),
                DeclarationHandle.Create(Prefix + "continuousState_fourier"),
                H("Continuous-time origin amplitude"),
                StatementSource.FromAuthor(Disp(Seq(Psi, Underscore, Grp(F.Id("C")), Open, F.Id("t"), Comma, F.Id("x"), Close, Sp, Eq, Sp, F.Id("s"), Sp, Sum, Underscore, Grp(F.Id("a")), Sp, F.Id("b"), Underscore, Grp(F.Id("a")), Open, F.Id("x"), Close, Sp, Exp, Open, F.Id("i"), Open, Rho, Underscore, Grp(F.Id("a")), Minus, D(1), Close, F.Id("t"), Close))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The source evolution in §3, printed p. 4, equation (10), is exp(−it(I−P)). Its origin column is the amplitude. The transition entry is p(x XOR z). The normalized Walsh vector b_a(x) is s times the character at a and s = 2^(−d/2). The factor s outside the sum is its value at the origin."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discretecomplexstate-eq-ofreal"),
                DeclarationHandle.Create(Prefix + "discreteComplexState_eq_ofReal"),
                H("Complex coined evolution"),
                StatementSource.FromAuthor(Disp(Seq(Psi, Underscore, Grp(F.Id("D")), Open, F.Id("n"), Comma, F.Id("y"), Comma, F.Id("x"), Close, Sp, Eq, Sp, F.Id("v"), Open, F.Id("n"), Comma, F.Id("y"), Comma, F.Id("x"), Close))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The right side is the real-coordinate state included in the complex numbers. The complex recurrence sums C(y,z) ψ(n,z,x XOR y) over z, with C(y,z) = 2√p(y)√p(z) − 1_{y=z}. Its initialization is 1_{x=0}√p(y). This is the shift after reflection in §4.2, printed p. 7. The equality is proved at every n, y and x."))),
                DescribeRole.Theorem))));
}
