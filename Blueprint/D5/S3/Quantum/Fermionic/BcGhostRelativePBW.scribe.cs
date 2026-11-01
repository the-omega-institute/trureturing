using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class BcGhostRelativePBWDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/BcGhostRelativePBW.";
    private static Formula V(string x) => F.Id(x);
    private static Formula C(string name, params Formula[] args)
    {
        var tokens = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (tokens.Count != 0) tokens.Add(Dot);
            tokens.Add(Operatorname); tokens.Add(Grp(F.Id(part)));
        }
        var fn = Seq(tokens.ToArray());
        return args.Length == 0 ? fn : new Formula.Apply(fn, [.. args]);
    }
    private static DocumentBlock Node(string name, Formula formula, string prose) => Describe.Lean(
        DescribeId.Create("bc-ghost-relative-pbw-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name.Replace("_", " ")),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original countable occupation carrier has a literal relative bc PBW basis and exact signed mode intertwinings.",
        H("Relative bc ghost PBW"), Blocks(
            Paragraph(Text("The relative ground state is the literal state c one vacuum, equal to ket of the singleton one. The relative carrier is the actual kernel of b zero. For finite positive integer sets B and C, W is the ascending ordered product of b minus r and c minus s acting from the right on that ground state.")),
            Node("relative_pbw_complete", C("relative_pbw_complete"), "The theorem gives the exact signed occupation formula, the inverse occupation bijection excluding site three, a linear equivalence from finitely supported pair coordinates onto the literal kernel of b zero, all four insertion and deletion actions for the integer modes, and the native occupation projections. The signs retain the b minus one particle hole and the crossing of the exceptional sites. Every object is the original CountableOccupationFock and BcGhostFock carrier; no PBW, spanning, independence, vacuum or coordinate replacement is assumed.")),
            Paragraph(Text("This is an algebraic relative ghost carrier result. It does not assert BRST nilpotence, quartet contraction, no-ghost, a complete string construction, a Monster or VOA identification, fusion, sewing, CFT completion, or an AdS/CFT theorem.")))));
}
