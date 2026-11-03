using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CircularWords;

internal sealed class DeletionReadoutReconstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CircularWords/DeletionReadoutReconstruction.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Labeled one-label deletions recover the orientation of a circle on at least four distinct labels.",
        H("Reconstruction from Labeled Circular Deletions"),
        Blocks(
            Paragraph(Text(
                "A circular word is a Mathlib Cycle: lists are identified under rotation and retain their orientation. "
                + "Fix a finite support A. SupportedCircle(A) consists of actual circles C with C.Nodup and C.toFinset = A. "
                + "The xth observation is CircularDeletionTransport.delete(x,C), the oriented residual obtained by "
                + "filtering out x. The deleted label remains the index of the observation. There is no assumed "
                + "injectivity, no quotient by reversal, and no unlabeled multiset of observations.")),
            Describe.Lean(DescribeId.Create("reconstruction"), DeclarationHandle.Create(Prefix + "reconstruct"),
                H("Four or More Labels Determine the Circle"),
                StatementSource.FromAuthor(ReconstructionFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Choose a label r in A and rotate both circles to begin with r. Write their representatives "
                    + "as r,a,L and r,b,K. They have at least four distinct labels, so there exists x in A distinct "
                    + "from r,a,b. Deleting x leaves representatives beginning with r,a and r,b. The existing "
                    + "CyclicInsertionGap.anchored_coe_injective theorem turns equality of their circular classes "
                    + "into equality of these lists, hence a = b. Now delete a itself. Since a occurs once, the "
                    + "residual representatives are r,L and r,K. Apply anchored uniqueness again to obtain L = K. "
                    + "This constructs reconstruction from the deletion equalities rather than assuming it."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("joint-kernel"), DeclarationHandle.Create(Prefix + "deletion_joint_kernel_iff"),
                H("The Exact Faithfulness Threshold"),
                StatementSource.FromAuthor(KernelFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Set X = SupportedCircle(A), take index type A, output type Cycle(Ambient), and define "
                    + "q(x,C) = delete(x,C). The reconstruction theorem proves that equal outputs for every index "
                    + "force equality in X. Applying JointFaithfulnessLeibnizCriterion.joint_faithfulness_tfae "
                    + "identifies the intersection of these observation kernels with the equality diagonal. For supports of "
                    + "at least three labels, this equality holds if and only if there are at least four labels: "
                    + "the opposite three-label orientations supply the failure direction. "
                    + "Thus the existing abstract concept-family criterion has a concrete circular-word application: "
                    + "joint readout loses no circular state, although each individual deletion forgets its insertion gap. "
                    + "The kernel statement concerns deterministic observations and does not assert a probability "
                    + "model, noisy-channel recovery, or a computational reconstruction bound."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For three distinct labels a,b,c, the circles [a,b,c] and [a,c,b] differ by orientation. "
                + "Anchored uniqueness proves they are distinct. Deleting any of a,b,c leaves the same two-label "
                + "circle, because its two possible list orders differ by rotation. This is the obstruction "
                + "used in the forward direction of the exact kernel threshold theorem.")))));

    private static Formula ReconstructionFormula()
    {
        Formula t = F.Id("T"), a = F.Id("A"), c = F.Id("C"), d = F.Id("D"), x = F.Id("x");
        Formula support = And(Eq(Call("support", c), a), Eq(Call("support", d), a));
        Formula deck = All("x", t, Imp(In(x,a), Eq(Call("delete", x,c), Call("delete",x,d))));
        return Disp(All("T",Call("Type"),Seq(OpenBracket,Call("DecidableEq",t),CloseBracket,Sp,
            All("A",Call("Finset",t),All("C",Call("Cycle",t),All("D",Call("Cycle",t),
                Imp(And(Le(D(4),Call("card",a)),And(Call("Nodup",c),And(Call("Nodup",d),And(support,deck)))),Eq(c,d))))))));
    }
    private static Formula KernelFormula()
    {
        Formula t=F.Id("T"),a=F.Id("A");
        Formula equality = Eq(Call("jointKernel",Call("deletionReadout",a)),Call("diagonal",Call("SupportedCircle",a)));
        Formula threshold = Iff(equality,Le(D(4),Call("card",a)));
        return Disp(All("T",Call("Type"),Seq(OpenBracket,Call("DecidableEq",t),CloseBracket,Sp,
            All("A",Call("Finset",t),Imp(Le(D(3),Call("card",a)),threshold)))));
    }
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(name),domain,body);
    private static Formula Eq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula In(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.MemberOf,b);
    private static Formula Le(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula And(Formula a,Formula b) => Logic(a,FormulaLogicOperator.And,b);
    private static Formula Iff(Formula a,Formula b) => Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Imp(Formula a,Formula b) => Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Logic(Formula a,FormulaLogicOperator op,Formula b) => new Formula.Logic(Seq(Open,a,Close),op,Seq(Open,b,Close));
}
