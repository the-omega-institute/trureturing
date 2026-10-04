using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class CanonicalChannelDPIDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Support-aware quantum relative entropy decreases under every finite quantum channel.",
        H("Canonical Quantum Channel Data Processing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-channel-relative-entropy-dpi"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/CanonicalChannelDPI.extended_quantum_relative_entropy_channel_dpi"),
                H("Data processing including singular noncommuting states"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Divergence/meiburg2026relative")),
                Blocks(
                    Paragraph(Text(
                        "The input and output carriers are arbitrary finite decidable nonempty "
                        + "types in independent universes. DensityState is the actual positive "
                        + "semidefinite complex matrix of trace one. QuantumChannel is a bundled "
                        + "completely positive complex-linear trace-preserving map, and mapState "
                        + "is its action on that same state.")),
                    Paragraph(Text(
                        "The entropy takes values in the real numbers with top adjoined. "
                        + "It equals Re Tr(rho (log rho - log sigma)) when ker(sigma) is contained "
                        + "in ker(rho), and top otherwise. The spectral logarithm uses natural "
                        + "logarithms and is totalized at zero. Singular states and noncommuting "
                        + "pairs remain in the theorem's scope.")),
                    Paragraph(Text(
                        "One Kraus family gives support transfer and both Schwarz inequalities. "
                        + "The positive-support eigenfamilies give exact trace-log coordinates "
                        + "and a contraction V satisfying V eta = xi, V* V <= I, and V* A V <= B. "
                        + "The square-root defect extends V to an isometry and annihilates eta.")),
                    Paragraph(Text(
                        "Reflection across the isometry range and finite eigenvector "
                        + "intertwining give logarithm compression. Operator logarithm "
                        + "monotonicity applies to strictly positive regularized matrices. "
                        + "A finite scalar logarithm limit then proves the supported inequality; "
                        + "the unsupported input has top on the right. This is the finite "
                        + "matrix form of the established Petz and Hiai-Mosonyi-Petz-Beny "
                        + "support contraction argument."))),
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

    private static Formula Instance(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula u = F.Id("u");
        Formula v = F.Id("v");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula mappedRho = Call("mapState", Phi, Rho);
        Formula mappedSigma = Call("mapState", Phi, SigmaLower);
        return Disp(Seq(
            Forall, Sp, u, Comma, Sp, v, Colon, Sp, Seq(Operatorname, Grp(F.Id("Level"))), Comma, Esc,
            a, Colon, Sp, type, Sp, u, Comma, Sp,
            b, Colon, Sp, type, Sp, v, Comma, Esc,
            Instance("Fintype", a), Comma, Sp,
            Instance("DecidableEq", a), Comma, Sp,
            Instance("Nonempty", a), Comma, Esc,
            Instance("Fintype", b), Comma, Sp,
            Instance("DecidableEq", b), Comma, Sp,
            Instance("Nonempty", b), Comma, Esc,
            Phi, Colon, Sp, Call("QuantumChannel", a, b), Comma, Esc,
            Rho, Comma, Sp, SigmaLower, Colon, Sp, Call("DensityState", a), Comma, Esc,
            Call("extendedQuantumRelativeEntropy", mappedRho, mappedSigma),
            Sp, Le, Sp, Call("extendedQuantumRelativeEntropy", Rho, SigmaLower), Dot));
    }
}
