using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk;

internal sealed class ShellCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/ShellCoefficients.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Hamming/ide2026scaling");

    private static Formula WalshMean(string walk) =>
        Seq(Mathbb, Grp(F.Id("E")), Underscore,
            Grp(F.Id("A"), Underscore, Grp(F.Id(walk), Comma, F.Id("d"))),
            OpenBracket, F.Id("c"), CloseBracket);

    private static Formula ShellSum(string summand) =>
        Seq(F.Id("W"), Underscore, Grp(F.Id("d"), Comma, F.Id("k")),
            Open, F.Id(summand), Close);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The shell profile determines the CT collision coefficient and the CT-minus-DT gap.",
        H("Krawtchouk eigenvalues and finite Walsh coefficients"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eigen-eq-krawtchouk"),
                DeclarationHandle.Create(Prefix + "eigen_eq_krawtchouk"),
                H("Eigenvalue at a Walsh character"),
                StatementSource.FromAuthor(Disp(Seq(Rho, Underscore, Grp(F.Id("k")), Sp, Eq, Sp, Sum, Underscore, Grp(F.Id("h"), Eq, D(0)), Caret, Grp(F.Id("d")), Sp, F.Id("w"), Underscore, Grp(F.Id("h")), Sp, F.Id("K"), Underscore, Grp(F.Id("h")), Open, F.Id("k"), Close, Slash, F.Id("N"), Underscore, Grp(F.Id("h"))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Here k is the Hamming weight of the character and N_h = choose(d,h). The weights are nonnegative and sum to one over 0 ≤ h ≤ d. An increment of weight h has mass w_h/N_h. The Krawtchouk polynomial K_h(k) sums (−1)^j choose(k,j) choose(d−k,h−j) over j = 0, …, min(h,k). This is the eigenvalue in §2.2, printed p. 4, equation (8)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-shell-gap"),
                DeclarationHandle.Create(Prefix + "finite_shell_gap"),
                H("The finite CT-minus-DT coefficient"),
                StatementSource.FromAuthor(Disp(Seq(
                    WalshMean("C"), Sp, Minus, Sp, WalshMean("D"), Sp, Eq, Sp, ShellSum("g")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A_{C,d} and A_{D,d} are the CT and DT position Cesàro laws. The expectations evaluate the Walsh character c of weight k ≤ d. The normalized sum W_{d,k}(f) counts (a,a XOR c). It is 2^(−d) times the sum over 0 ≤ i ≤ d−k and 0 ≤ j ≤ k, with weight choose(d−k,i) choose(k,j) on f(i+j,i+k−j). The summand g(u,v) is (1−ρ_k)/(2(1−ρ_u²)) for equal interior eigenvalues ρ_u = ρ_v and zero elsewhere. The gap is between zero and one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-shell-collisions"),
                DeclarationHandle.Create(Prefix + "finite_shell_collisions"),
                H("The finite CT collision coefficient"),
                StatementSource.FromAuthor(Disp(Seq(WalshMean("C"), Sp, Eq, Sp, ShellSum("b")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The expectation evaluates the Walsh character c under the CT position Cesàro law A_{C,d}. The summand b(u,v) is 1 when ρ_u = ρ_v and 0 otherwise. It counts coincidences across different shells and both equal endpoints. The DT coefficient is the CT coefficient minus the gap in the preceding identity. The owner also proves both formulas as limits of the actual finite-horizon observables."))),
                DescribeRole.Theorem))));
}
