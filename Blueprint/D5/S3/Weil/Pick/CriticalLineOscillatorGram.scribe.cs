using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class CriticalLineOscillatorGramDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Pick/CriticalLineOscillatorGram.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A reflected critical-line pole pair generates a finite positive Pick Gram matrix "
            + "with a two-row factor.",
        H("Critical-Line Oscillator Gram Matrix"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("critical-line-oscillator-feature-matrix"),
                DeclarationHandle.Create(Prefix + "criticalLineOscillatorFeatureMatrix"),
                H("Reflected oscillator feature matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two rows sample the resolvents at the reflected imaginary poles "
                        + "plus and minus i times the real ordinate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("critical-line-oscillator-pick-matrix"),
                DeclarationHandle.Create(Prefix + "criticalLineOscillatorPickMatrix"),
                H("Finite oscillator Pick matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Pick atom is defined as the conjugate-transpose Gram product of "
                        + "the two reflected resolvent rows. Its rank is at most two, with "
                        + "possible degeneracy."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("critical-line-oscillator-pick-gram"),
                DeclarationHandle.Create(Prefix + "critical_line_oscillator_pick_gram"),
                H("The oscillator Pick matrix is positive semidefinite"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The preceding definition owns the Gram factorization.")),
                    Paragraph(Text(
                        "Mathlib's conjugate-transpose Gram theorem proves positive "
                            + "semidefiniteness for every finite family of complex nodes, "
                            + "including repeated nodes and nodes at a pole under the totalized "
                            + "inverse convention."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula carrier = F.Id("I");
        Formula gamma = F.Id("gamma");
        Formula nodes = F.Id("nodes");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula carrierType = Seq(Operatorname, Grp(F.Id("Type")));
        Formula nodeMap = Seq(carrier, Sp, Mapsto, Sp, complex);
        Formula pick = Call(
            "criticalLineOscillatorPickMatrix", gamma, nodes);

        return Disp(Seq(
            Forall, Sp, carrier, Colon, Sp, carrierType, Comma, Sp,
            gamma, Sp, InMacro, Sp, reals, Comma, Sp,
            nodes, Colon, Sp, nodeMap, Comma, RowBreak, Grp(),
            Call("Fintype", carrier), Sp, Rightarrow, RowBreak, Grp(),
            Call("PosSemidef", pick), Dot));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(Comma);
                pieces.Add(Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq(pieces.ToArray());
    }
}
