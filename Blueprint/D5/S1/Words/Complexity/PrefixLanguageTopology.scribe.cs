using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class PrefixLanguageTopologyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closed one-sided word sets are recovered from finite prefix cylinders, and shift invariance descends to finite stages.",
        H("Finite Prefix Reflection for Infinite Word Sets"),
        Blocks(
            Paragraph(Text(
                "For a set S of one-sided words over a discrete alphabet, prefixCylinder S n "
                    + "collects the length-n cylinders through S. These finite observations "
                    + "reconstruct every closed S and provide the transition law for a forward shift.")),
            Describe.Lean(
                DescribeId.Create("prefix-cylinder-open"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/PrefixLanguageTopology.isOpen_prefixCylinder"),
                H("Finite prefix cylinders are open"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("IsOpen")), Sp,
                    F.Id("prefixCylinder"), Sp, F.Id("S"), Sp, F.Id("n")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The set is a union of product cylinders, so the discrete product basis "
                        + "makes openness immediate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prefix-cylinder-closed"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/PrefixLanguageTopology.isClosed_prefixCylinder"),
                H("Finite prefix cylinders are closed"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("IsClosed")), Sp,
                    F.Id("prefixCylinder"), Sp, F.Id("S"), Sp, F.Id("n")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The complement is the union of cylinders with the same finite "
                        + "prefix length, so it is open in the discrete product basis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("closed-prefix-reflection"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/PrefixLanguageTopology.closed_eq_iInter_prefixCylinder"),
                H("Closed sets are reconstructed by all finite prefixes"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("S"), Sp, Eq, Sp, F.Id("intersection"), F.Id("n"), Sp,
                    F.Id("prefixCylinder"), Sp, F.Id("S"), Sp, F.Id("n")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A point outside a closed set is excluded by one finite cylinder from the "
                        + "product basis; a point in the set supplies a witness at every level."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("closure-prefix-reflection"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/PrefixLanguageTopology.closure_eq_iInter_prefixCylinder"),
                H("All finite prefixes reconstruct the closure"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("closure"), Sp, F.Id("S"), Sp, Eq, Sp,
                    F.Id("intersection"), F.Id("n"), Sp,
                    F.Id("prefixCylinder"), Sp, F.Id("S"), Sp, F.Id("n")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each prefix approximation is clopen, so their intersection is closed; "
                        + "the product basis separates every point outside the closure."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shift-prefix-transition"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/PrefixLanguageTopology.shift_mem_prefixCylinder_of_mem_succ"),
                H("Shift invariance descends one prefix stage"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("x"), Sp, InMacro, Sp, F.Id("prefixCylinder"), Sp,
                    F.Id("S"), Sp, F.Id("n"), Plus, D(1), Sp, Rightarrow, Sp,
                    F.Id("shift"), Sp, F.Id("x"), Sp, InMacro, Sp,
                    F.Id("prefixCylinder"), Sp, F.Id("S"), Sp, F.Id("n")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Agreement through n+1 coordinates transports to agreement through n "
                        + "coordinates after dropping the first coordinate."))),
                DescribeRole.Theorem))));
}
