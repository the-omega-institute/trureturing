using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Quandles;

internal sealed class BlockCountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/Quandles/BlockCounting.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/ta2025goodinvolutions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete conjugacy partition and its central twisted-inversion blocks factor the count of all good maps.",
        H("BlockCounting"),
        Blocks(
            Describe.Lean(DescribeId.Create("ta116-data"),
                DeclarationHandle.Create(Prefix + "Data"), H("A complete block certificate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Data records representatives, a conjugacy-invariant classifier, a conjugator from the classified representative to every element, an equivalence with the actual center, and every central twisted-inversion destination. It assumes no counts."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ta116-local"),
                DeclarationHandle.Create(Prefix + "Local"), H("All compatible labels on one block"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a block C_b and center alphabet Z, Local consists of every function f:C_b→Z satisfying f(dest(b,i,f(i)))=f(i) for every i. When two classes are paired, their common central label is chosen once."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ta116-labelblockequiv"),
                DeclarationHandle.Create(Prefix + "labelBlockEquiv"), H("Global labels are independent local assignments"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The representatives restrict a global central label to each block. The classifier extends local assignments to all group elements. The conjugator and center equivalence prove that restriction and extension are mutual inverses. This includes all labels, not a selected subfamily."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ta116-good-card"),
                DeclarationHandle.Create(Prefix + "good_card"), H("The complete product formula"),
                CountStatement(false), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For any group G, complete certificate D:Data G B Z C, and finite set B of blocks, the cardinality of all good maps is the product of the cardinalities of the local compatible-label types. Empty and zero-count blocks are included. Each local factor is the central-label form of the weighted involution sum; a paired edge carries one common label."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ta116-whole-good-card"),
                DeclarationHandle.Create(Prefix + "whole_good_card"), H("The product formula on the existing interface"),
                CountStatement(true), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For finite G with decidable equality, WholeGood(G) in the display abbreviates the existing Good subtype on Finset.univ. The same exact product formula applies to it. It is used by both numerical counts in the complete Problem 11.6 refutation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ta116-classequiv"),
                DeclarationHandle.Create(Prefix + "classEquiv"), H("The native conjugacy-class quotient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The certificate gives an equivalence from Mathlib ConjClasses G to the disjoint union of block indices. Thus the class count used in the refutation is the actual class number."))), DescribeRole.Definition))));
    private static StatementSource CountStatement(bool whole) => StatementSource.FromAuthor(
        F.Disp(new Formula.Relation(Call("NatCard", Call(whole ? "WholeGood" : "Good", F.Id("G"))),
            FormulaRelationOperator.Equal,
            F.Seq(F.Prod, F.Underscore, F.Grp(F.Id("b"), F.InMacro, F.Sp, F.Id("B")), F.Sp,
                Call("NatCard", Call("Local", Call("dest", F.Id("D")), F.Id("b")))))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Seq(F.Operatorname, F.Grp(F.Id(name))), [.. arguments]);
}
