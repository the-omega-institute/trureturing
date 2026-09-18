using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class ResidueHeightUpperBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every complete prime-power residue node admits an identifying passive protocol "
            + "with at most (e-d)(p-1) queries on every target.",
        H("Uniform Height Bound for Residue Identification"),
        Blocks(
            Paragraph(Text(
                "Let p be prime and let e and d be natural numbers with d at most e. "
                    + "For a label b in ZMod(p^d), B is the node of residues in X=ZMod(p^e) "
                    + "whose depth-d projection is b. Its remaining height is e-d. "
                    + "Tree means PassiveProtocol X with natural-number answers. The sensor "
                    + "q(c,a)=residueReadout(p,e,c,a) returns the greatest congruence depth "
                    + "of its center and target, including zero and e. R(T,a) means "
                    + "runPassiveProtocol q T a; it records both centers and their actual answers.")),
            Describe.Lean(
                DescribeId.Create("residue-height-upper-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Budget/ResidueHeightUpperBound.residue_height_upper_bound"),
                H("An identifying tree with a uniform bound on realized traces"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The tree exists for every label and every allowed depth. Ident(B,T) "
                            + "means that equal complete traces of targets in B imply equal "
                            + "targets. The length bound holds separately for every target "
                            + "in B, without an averaging measure or an assumed family of "
                            + "bounded child trees. Centers remain actual residues in X.")),
                    Paragraph(Text(
                        "Induct on the remaining height. At height zero the node has one "
                            + "element, and the stop tree suffices. At height one its p leaves "
                            + "have an arbitrary enumeration. The leaf protocol realizes "
                            + "the capped position lengths, at most p-1; its existence follows "
                            + "by assigning constant positive mass to all leaves.")),
                    Paragraph(Text(
                        "At greater heights the induction hypothesis constructs an identifying "
                            + "bounded tree for each of the p complete children. Extracting the "
                            + "chronological prefix for a singleton child gives a tree headed "
                            + "inside that child. Removing this constant prefix cannot increase "
                            + "any realized length. The child is nonleaf, so the extracted "
                            + "tree has the required head. Splicing these actual trees in any "
                            + "child order yields an identifying parent tree. For a target "
                            + "in position i, numbered from zero, the trace has exactly i "
                            + "failed sibling entries followed by its child trace. Since "
                            + "i is at most p-1, its length is at most (p-1)+(e-d-1)(p-1). "
                            + "The final child needs no additional entry query.")),
                    Paragraph(Text(
                        "For any strictly positive normalized rational prior, transport this "
                            + "tree to its full-history selector. The transport preserves each "
                            + "complete terminal trace and its length. Hence at every integer "
                            + "horizon t at least (e-d)(p-1), this eventually zero-error "
                            + "terminating selector succeeds on all of B. Every selector's "
                            + "successful mass is bounded above by the total mass of B, so "
                            + "the maximum over all original selectors equals that total mass. "
                            + "No cutoff truncation or deletion of delays in arbitrary selectors "
                            + "is needed. In particular the statement includes p=2, e=0 "
                            + "and d=e. It asserts no evaluator or runtime bound."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Budget/ResidueChildPrefixStructure")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Budget/ResidueLeafOptimality")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Budget/ResiduePosteriorClosure")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Budget/ResidueFirstStepOptimality")),
        ]));

    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] args) => Call(s, args);
    private static Formula All(Formula x, Formula set, Formula body) =>
        Seq(Forall, Sp, x, Sp, InMacro, Sp, set, Comma, Sp, body);
    private static Formula Par(Formula x) => Seq(Left, Open, x, Right, Close);

    private static Formula Statement()
    {
        var p = V("p"); var e = V("e"); var d = V("d"); var b = V("b");
        var t = V("T"); var a = V("a"); var nat = Seq(Mathbb, Grp(V("N")));
        var node = C("node", p, e, d, b);
        var length = C("len", C("R", t, a));
        var bound = Seq(Par(Seq(e, Minus, d)), Par(Seq(p, Minus, D(1))));
        var conclusion = Seq(Exists, Sp, t, Sp, InMacro, Sp, V("Tree"), Comma, Sp,
            C("Ident", node, t), Sp, Land, Sp,
            All(a, node, Seq(length, Sp, Leq, Sp, bound)));
        return All(p, nat, All(e, nat,
            Seq(C("Prime", p), Sp, Rightarrow, Sp,
                All(d, nat, Seq(Par(Seq(d, Sp, Leq, Sp, e)), Sp, Rightarrow, Sp,
                    All(b, C("ZMod", Seq(p, Caret, Grp(d))), conclusion))))));
    }
}
