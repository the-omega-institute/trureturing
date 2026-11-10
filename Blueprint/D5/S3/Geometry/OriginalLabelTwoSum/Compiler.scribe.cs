using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class CompilerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Compiler.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/Compiler",
            "The original Gamma/two-filling compiler constructs a computed parent certificate with separate main and core sequences.",
            "original-label-two-sum-compiler",
            Anchor.ParseCanonical("mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic")),
        H("Compiler"),
        Blocks(
            Node("compilerpermission", "CompilerPermission", "CompilerPermission",
                "The exact original permission: Gamma, or no vertical pair in EITHER actual child list together with a core vertex different from the interface.", DescribeRole.Definition),
            Node("finishcore", "finishCore", "finishCore",
                "The terminal core schedule returns an ORIGINAL parent vertex. The e=p case consumes genuine Gamma and the nonempty original R. It also covers X=empty.", DescribeRole.Definition),
            Node("compileparent", "compileParent", "compileParent",
                "Full original parent constructor on literal original grounds. Main uses the child main and P0/P1. Separate starts on Cout ALONE, uses Q0/Q1, the child core list, and the computed terminal cone/Gamma list. Cout and critical faces are filled from their explicit constructions, rather than supplied as hypotheses.", DescribeRole.Definition),
            Node("compileparent-critical", "compileParent_critical", "compileParent_critical",
                "The exact computed critical family is exposed by reduction of the actual constructor. This equation is consumed by the wheel one-step consequences.", DescribeRole.Theorem),
            Node("compiler-main-fixed", "compiler_main_fixed", "compiler_main_fixed",
                "Whole-endpoint coordinate fixedness uses the real native homotopy; no parallel simulated realization or homotopy is introduced.", DescribeRole.Theorem),
            Node("collapsecone-orderedpairs", "collapseCone_orderedPairs", "collapseCone_orderedPairs",
                "The descending cone is an actual rectangle on the original ground.", DescribeRole.Theorem),
            Node("finishvertex", "finishVertex", "finishVertex",
                "The actual original terminal vertex, specified independently of any certificate: preserve p away from e, otherwise use the same finite choice as terminalAtInterface.", DescribeRole.Definition),
            Node("finishfacepairs", "finishFacePairs", "finishFacePairs",
                "The entire terminal face list on the full original ground. Gamma is used only when e=p and X is nonempty; the X-empty case is the original Y-simplex.", DescribeRole.Definition),
            Node("finishpairschedule", "finishPairSchedule", "finishPairSchedule",
                "The terminal block selected by `finishCore`, with both the e=p Gamma branch and the original-vertex cone branch made explicit.", DescribeRole.Definition),
            Node("finishpairschedule-faces", "finishPairSchedule_faces", "finishPairSchedule_faces",
                "Proof irrelevance identifies the chosen right Gamma from any existing Nonempty permission with the same choice in rightGammaPairs. No equality with a particular supplied witness is asserted.", DescribeRole.Theorem),
            Node("finishcore-orderedpairs", "finishCore_orderedPairs", "finishCore_orderedPairs",
                "Exact list extraction for the private terminal constructor in the same owner. The proof follows its two tests and uses only the actual cone and Gamma/fibre schedules.", DescribeRole.Theorem),
            Node("compileparent-vertex", "compileParent_vertex", "compileParent_vertex",
                "Computed parent vertex is consumed by the independent row seed recursion.", DescribeRole.Theorem),
            Node("compileparent-main-orderedpairs", "compileParent_main_orderedPairs", "compileParent_main_orderedPairs",
                "Full main list: child-main replay, then the ordered filling blocks.", DescribeRole.Theorem),
            Node("compileparent-separate-orderedpairs", "compileParent_separate_orderedPairs", "compileParent_separate_orderedPairs",
                "Full separate/core list: collars on `Cout` alone, child-core replay, then the original-vertex cone/Gamma terminal block, including e=p and X=∅.", DescribeRole.Theorem),
            Node("parentexpansion", "ParentExpansion", "ParentExpansion",
                "Public endpoint consumed by row-history code. The two equalities are kept together so neither the main nor the separate recursion can be dropped.", DescribeRole.Definition),
            Node("compileparent-consumed-expansion", "compileParent_consumed_expansion", "compileParent_consumed_expansion",
                "Original-label source declaration consumed by the native compiler and row construction.", DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            role == DescribeRole.Definition ? StatementSource.WithoutFormula() : StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(SourceText(prose)), role);

    // TextRun is one line. Keep every quoted source line, including blank separators,
    // as typed text; this is commentary, never a substitute for a Lean projection.
    private static DocumentBlock SourceText(string value) => value.Contains('\n')
        ? new DocumentBlock.Section(H("Source text"), Blocks(Array.ConvertAll(
            value.Split('\n'), line => Paragraph(Text(line.Length == 0 ? "Definitions and proofs are in the paired Lean module." : line)))))
        : Paragraph(Text(value));
}
