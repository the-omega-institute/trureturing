using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.FutureResponses;

internal sealed class NativeJointFutureClassesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A native source is an ordered binary tree with alpha and beta leaves. Substitution sends alpha to beta, beta to the ordered pair beta-alpha, and acts on both children of a branch. The initial source is the pair of alpha and an arbitrary finite right subtree. The supplied count is the same for both addresses RL and RR.",
        H("Native Joint Future Classes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nativejointfutureclasses"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/FutureResponses/NativeJointFutureClasses.native_joint_future_classification"),
                H("Native Joint Future Classes"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Forall, Sp, F.Id("u"), Comma, F.Id("v"), Colon, F.Id("Source"), Comma,
                    Open, Forall, Sp, F.Id("k"), InMacro, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma,
                    C("futureReplies", F.Id("u"), F.Id("k")), Eq,
                    C("futureReplies", F.Id("v"), F.Id("k")), Close, Leftrightarrow, Sp,
                    C("jointClass", F.Id("u")), Eq, C("jointClass", F.Id("v")), Close,
                    Land, Sp, C("Surjective", F.Id("jointClass")), Land, Sp,
                    C("card", F.Id("JointClass")), Eq, D(1, 1)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A native source is an ordered binary tree with alpha and beta leaves. Substitution sends alpha to beta, beta to the ordered pair beta-alpha, and acts on both children of a branch. The initial source is the pair of alpha and an arbitrary finite right subtree. The supplied count is the same for both addresses RL and RR.")),
                    Paragraph(Text("The right subtree has two leaf classes. If it is a branch, the complete future reply at each child is determined by whether that child initially is alpha, beta or a branch. These nine pairs are jointly realized by pairing canonical root representatives inside one source. A branch stays a branch for every future count. The two leaf cases and the nine branch cases are distinct; no bound on the tree height or on the future count is imposed.")),
                    Paragraph(Text("Equality of the two reply trajectories at every supplied count is equivalent to equality of the eleven-valued joint class. Generic minimum sufficient coding is supplied by target_family_minimal_quotient; the native calculation specifies its attained joint fibers.")),
                    Paragraph(Text("For an acquisition consumer, v must be supplied by a selected occurrence in the same actual source U, not extracted from an unrelated representative. The root selection U=mul(of true,v) makes the correspondence to the two actual RL/RR replies literal for every count. A source without that selected root has no label under this selection and remains in the acquisition domain. The boundedSources(4) root slice cannot attain the branch/branch pair because its full source would need at least five leaves. The all-source eleven-class theorem does not assert eleven attained labels in every bounded slice.")),
                    Paragraph(Text("This observation quotient forgets descendants and acquisition history. The actual numbered-path response quotient instead compares full resulting states, including any retained immutable source, chronological prefix and returned phase. The two quotients need no common equivalence relation: matching native labels alone supplies neither action-enabledness, target-certificate reuse nor equality of full successor states. The owning ActualTreeReadoutAcquisition exposition specifies an actual Next/Return lift and the separate completion and cost obligations."))),
                DescribeRole.Theorem))));

    private static Formula C(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
