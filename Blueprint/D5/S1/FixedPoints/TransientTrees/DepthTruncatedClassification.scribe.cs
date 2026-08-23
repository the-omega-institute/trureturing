using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.FixedPoints.TransientTrees;

internal sealed class DepthTruncatedClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-depth branch codes classify truncated transient trees and truncate naturally.",
        H("Depth-Truncated Transient-Tree Classification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("depth-truncated-tree-classification-and-naturality"),
                DeclarationHandle.Create(
                    "D5/S1/FixedPoints/TransientTrees/DepthTruncatedClassification."
                        + "depth_truncated_tree_classification_and_naturality"),
                H("Depth codes classify and form a compatible inverse system"),
                StatementSource.FromAuthor(StatementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let tau and sigma be self-maps of finite carriers. At depth zero the "
                            + "branch code retains only the root. Each successor depth is the "
                            + "unordered multiset of the preceding-depth codes of every actual "
                            + "nonperiodic predecessor.")),
                    Paragraph(Text(
                        "The truncated rooted-tree relation is defined independently by a "
                            + "one-to-one recursive matching of those predecessor multisets. "
                            + "Induction on depth identifies that relation exactly with equality "
                            + "of the corresponding branch codes.")),
                    Paragraph(Text(
                        "Periodic roots are grouped by Mathlib's cyclic periodic orbit. Each "
                            + "component cycle is decorated by its rooted depth codes, and the "
                            + "multiset retains repeated equal necklaces coming from distinct "
                            + "components.")),
                    Paragraph(Text(
                        "The named truncation maps every child code recursively, every necklace "
                            + "site through the cycle map, and every component through the "
                            + "multiset map. It therefore sends both each depth-successor root "
                            + "code and the full decorated invariant to the preceding depth."))),
                DescribeRole.Theorem))));

    private static Formula StatementFormula()
    {
        Formula carrierY = F.Id("Y");
        Formula carrierZ = F.Id("Z");
        Formula updateY = Tau;
        Formula updateZ = SigmaLower;
        Formula depth = F.Id("h");
        Formula rootY = F.Id("y");
        Formula rootZ = F.Id("z");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula codeY = Call("depthBranchCode", updateY, depth, rootY);
        Formula codeZ = Call("depthBranchCode", updateZ, depth, rootZ);
        Formula nextCodeY = Call(
            "depthBranchCode", updateY, Seq(depth, Plus, D(1)), rootY);
        Formula invariant = Call("depthInvariant", depth, updateY);
        Formula nextInvariant = Call(
            "depthInvariant", Seq(depth, Plus, D(1)), updateY);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, carrierY, Comma, Sp, carrierZ, Colon, Sp, type, Comma, RowBreak, Grp(),
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, carrierY, Close,
            CloseBracket, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, carrierZ, Close,
            CloseBracket, Comma, RowBreak, Grp(),
            updateY, Colon, Sp, carrierY, Sp, To, Sp, carrierY, Comma, Sp,
            updateZ, Colon, Sp, carrierZ, Sp, To, Sp, carrierZ, Comma, RowBreak, Grp(),
            depth, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, RowBreak, Grp(),
            Open,
            Forall, Sp, rootY, Colon, Sp, carrierY, Comma, Sp,
            rootZ, Colon, Sp, carrierZ, Comma, Sp,
            Call(
                "TruncatedRootedTreeIsomorphic",
                updateY,
                updateZ,
                depth,
                rootY,
                rootZ),
            Sp, Iff, Sp, codeY, Sp, Eq, Sp, codeZ,
            Close, RowBreak, Grp(),
            Land, RowBreak, Grp(),
            Open,
            Forall, Sp, rootY, Colon, Sp, carrierY, Comma, Sp,
            Call("truncateBranchCode", depth, nextCodeY),
            Sp, Eq, Sp, codeY,
            Close, RowBreak, Grp(),
            Land, RowBreak, Grp(),
            Call("truncateDepthInvariant", depth, nextInvariant),
            Sp, Eq, Sp, invariant, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
