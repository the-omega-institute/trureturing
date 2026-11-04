using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class LiLiZhaoFiniteCRTDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite prime-residue cylinders supply the compatibility bridge for the Li--Li--Zhao prime-tail topology construction.",
        H("Prime-tail topology bridge"),
        Blocks(
            Paragraph(Text("For the increasing enumeration p_i of the prime numbers, every finite assignment of residue classes modulo p_i has a simultaneous natural-number solution by the Chinese remainder theorem.")),
            Describe.Lean(
                DescribeId.Create("finite-crt"),
                DeclarationHandle.Create("D5/S3/Topology/LiLiZhaoFiniteCRT.finite_crt"),
                H("Finite Chinese-remainder compatibility"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The proof uses Mathlib's finite Chinese-remainder construction together with pairwise coprimality of distinct entries in the prime enumeration."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-cylinder-nonempty"),
                DeclarationHandle.Create("D5/S3/Topology/LiLiZhaoFiniteCRT.finiteCylinder_nonempty"),
                H("Every finite cylinder is nonempty"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite cylinder is the intersection of finitely many prime residue classes, so the previous theorem gives a witness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("disjoint-cylinders-nonempty"),
                DeclarationHandle.Create("D5/S3/Topology/LiLiZhaoFiniteCRT.disjoint_cylinders_nonempty"),
                H("Disjoint supports still have a common point"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When two finite cylinders use disjoint prime indices, their assignments can be merged and solved by one CRT instance. This is the finite-pattern step used later in the common-open topology."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tail-subbasis"),
                DeclarationHandle.Create("D5/S3/Topology/LiLiZhaoFiniteCRT.tailSubbasis"),
                H("Prime-tail subbases"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The subbasis at level n contains the residue classes for all prime indices i at least n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tail-topology-t2"),
                DeclarationHandle.Create("D5/S3/Topology/LiLiZhaoFiniteCRT.tailTopology_t2"),
                H("Every prime-tail topology is Hausdorff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A sufficiently large prime index separates two distinct naturals by disjoint residue classes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-cylinder-basis"),
                DeclarationHandle.Create("D5/S3/Topology/LiLiZhaoFiniteCRT.finiteCylinder_basis_of_isOpen"),
                H("Finite cylinders form local basic neighborhoods"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Induction on generated opens extracts a finite cylinder through every point of an open set and contained in that open set."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("common-t1"),
                DeclarationHandle.Create("D5/S3/Topology/LiLiZhaoFiniteCRT.commonTopology_t1"),
                H("The common topology is T1"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Closed singletons persist through the infimum of the tail topologies."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("common-irreducible"),
                DeclarationHandle.Create("D5/S3/Topology/LiLiZhaoFiniteCRT.commonTopology_univ_irreducible"),
                H("The whole space is irreducible in the common topology"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The local finite-cylinder basis and CRT compatibility force any two nonempty common opens to intersect."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("common-not-quasi-sober"),
                DeclarationHandle.Create("D5/S3/Topology/LiLiZhaoFiniteCRT.commonTopology_not_quasiSober"),
                H("The common topology is not quasi-sober"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The T1 property makes every singleton closed and equal to its closure, while the whole space is a larger irreducible closed set."))),
                DescribeRole.Theorem),
            Paragraph(Text("This formally captures the paper's counterexample: a decreasing prime-tail chain of Hausdorff topologies whose common topology is T1, irreducible, and non-quasi-sober.")) )));
}
