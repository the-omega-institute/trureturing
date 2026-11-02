using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class RelativeFrattiniKernelDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/cfsg2026frattinikernel");
    private const string Owner = "D5/S3/FiniteGroups/RelativeFrattiniKernel.";
    private static Formula Q => F.Id("Q");
    private static Formula P => F.Id("P");
    private static Formula Prime => F.Id("p");
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula BaseGroup(Formula body) =>
        All("Q", F.Id("Type"), Instance(Call("Group", Q), body));
    private static Formula SubgroupContext(Formula body) =>
        BaseGroup(All("P", Call("Subgroup", Q), body));
    private static Formula NormalSubgroupContext(Formula body) =>
        SubgroupContext(Instance(Call("Normal", P), body));
    private static Formula Eq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Hypotheses(Formula body) =>
        All("Q", F.Id("Type"), All("group", Call("Group", Q),
        All("finite", Call("Finite", Q), All("P", Call("Subgroup", Q),
        All("normal", Call("Normal", P), All("p", F.Id("Nat"),
        All("pgroup", Call("IsPGroup", Prime, P), body)))))));
    private static Formula A => Call("preservingAut", P);
    private static Formula Fr => Call("relativeFrattini", P);
    private static Formula Rho => Call("quotientAction", P);
    private static Formula BarRho => Call("outerAction", P);
    private static Formula OutP => Call("RelativeOuter", P);
    private static Formula Quot => Call("Quotient", Q, Fr);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The automorphism and outer-automorphism kernels of a normal prime-power subgroup are prime-power groups.",
        H("Relative Frattini Kernels"),
        Blocks(
            Describe.Lean(DescribeId.Create("preserving-automorphisms"),
                DeclarationHandle.Create(Owner + "preservingAut"),
                H("Automorphisms preserving a specified subgroup"),
                StatementSource.FromAuthor(Disp(SubgroupContext(Eq(A, Call("Stabilizer", Call("MulAut", Q), P))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let Q be a group and P a specified subgroup. The group A consists of all automorphisms a of Q for which x belongs to P exactly when a(x) belongs to P. No characteristic-subgroup assumption is imposed on P."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("relative-frattini-subgroup"),
                DeclarationHandle.Create(Owner + "relativeFrattini"),
                H("The common subgroup inside the ambient group"),
                StatementSource.FromAuthor(Disp(SubgroupContext(Eq(Fr, Call("map", Call("frattini", P), Call("subtype", P)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write F for the image of Frattini(P) under the inclusion of P in Q. If P is normal in Q, then F is normal in Q, since Frattini(P) is characteristic in P. Every element of A preserves F."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("restriction-action"),
                DeclarationHandle.Create(Owner + "restriction"),
                H("Restriction to P"),
                StatementSource.FromAuthor(Disp(SubgroupContext(All("a", A, All("x", P,
                    Eq(Call("apply", Call("restriction", P, F.Id("a")), F.Id("x")),
                        Call("apply", F.Id("a"), F.Id("x")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Restriction is a homomorphism from A to Aut(P). Its inverse on each individual automorphism is the restriction of that automorphism's inverse."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("relative-quotient-action"),
                DeclarationHandle.Create(Owner + "quotientAction"),
                H("The induced action on the actual quotient"),
                StatementSource.FromAuthor(Disp(NormalSubgroupContext(All("a", A, All("x", Q,
                    Eq(Call("apply", Call("apply", Rho, F.Id("a")), Call("coset", F.Id("x"), Fr)),
                        Call("coset", Call("apply", F.Id("a"), F.Id("x")), Fr))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The homomorphism rho from A to Aut(Q/F) sends the coset of x to the coset of a(x). Its kernel B is exactly the group of all P-preserving automorphisms inducing the identity on Q/F."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("relative-automorphism-kernel"),
                DeclarationHandle.Create(Owner + "isPGroup_automorphism_kernel"),
                H("The full automorphism kernel is a prime-power group"),
                StatementSource.FromAuthor(Disp(Hypotheses(Call("IsPGroup", Prime, Call("ker", Rho))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Assume Q is finite and P is a normal p-subgroup. The result is proved for every natural p satisfying IsPGroup p P; in particular it applies to every prime p. It includes P trivial, P equal to Q, trivial Frattini subgroup, noncharacteristic P, nonabelian P, nonsplit extensions and nontrivial conjugation actions.")),
                    Paragraph(Text("Restrict B to P. Its image lies in the ordinary Frattini automorphism kernel of P: triviality modulo the image F inside Q pulls back to triviality modulo Frattini(P). The ordinary finite Frattini kernel theorem therefore makes this image a p-group.")),
                    Paragraph(Text("Let K be the restriction kernel. Every a in K fixes P pointwise and satisfies x inverse times a(x) in F, hence in P. Define its displacement as the function d(a) from Q to P. Pointwise fixation makes displacement multiplicative under composition, even when P is nonabelian.")),
                    new DocumentBlock.DisplayFormula(Disp(All("a", F.Id("K"), All("b", F.Id("K"), All("x", Q,
                        Eq(Call("d", Call("mul", F.Id("a"), F.Id("b")), F.Id("x")),
                            Call("mul", Call("d", F.Id("a"), F.Id("x")), Call("d", F.Id("b"), F.Id("x"))))))))),
                    Paragraph(Text("The displacement is injective because its values recover a(x) for every x. A single p-power annihilates every element of finite P, so it also annihilates every function Q to P. Thus K is a p-group. The kernel-image extension argument proves that B is a p-group. The displacement method follows Theory/GroupTheory/CentralCharacteristicAutomorphisms.lean of Qiuzhen-CFSG/CFSG at revision 0c6635528a02dd46f2e93e2ade0c4ac647ad1eb7, under Apache-2.0, with the ambient automorphism group restricted to A. The ordinary Frattini theorem is reused directly."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("relative-outer-group"),
                DeclarationHandle.Create(Owner + "RelativeOuter"),
                H("The actual relative outer automorphism group"),
                StatementSource.FromAuthor(Disp(NormalSubgroupContext(Eq(OutP, Call("Quotient", A, Call("relativeInner", P)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any group G, innerAut G is the image of conjugation G to Aut(G), and OuterAut G is Aut(G) modulo that normal subgroup. The subgroup relativeInner P is the inverse image of innerAut Q under the inclusion A into Aut(Q). Since P is normal, all inner automorphisms of Q lie in A. RelativeOuter P is therefore the group of P-preserving outer automorphisms, with its actual inner equivalence relation."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("relative-outer-action"),
                DeclarationHandle.Create(Owner + "outerAction"),
                H("The homomorphism on outer automorphisms"),
                StatementSource.FromAuthor(Disp(NormalSubgroupContext(All("a", A,
                    Eq(Call("apply", BarRho, Call("coset", F.Id("a"), Call("relativeInner", P))),
                        Call("coset", Call("apply", Rho, F.Id("a")), Call("innerAut", Quot))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An inner automorphism represented by q in Q induces conjugation by qF on Q/F. Consequently rho descends to a homomorphism from RelativeOuter P to OuterAut(Q/F). Both sides use the same Q, P and F as the automorphism theorem."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("all-relative-outer-kernels"),
                DeclarationHandle.Create(Owner + "isPGroup_outer_kernel"),
                H("Every restricted outer-action kernel is a prime-power group"),
                StatementSource.FromAuthor(Disp(Hypotheses(All("H", Call("Subgroup", OutP),
                    Call("IsPGroup", Prime, Call("ker", Call("comp", BarRho, Call("subtype", F.Id("H"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let H be any subgroup of the relative outer group. Its restricted map to OuterAut(Q/F) has a p-group kernel. To prove this, represent an element of the full outer kernel by a in A. The induced automorphism rho(a) is conjugation by some y in Q/F. Lift y to q in Q and multiply a by the inverse of conjugation by q.")),
                    new DocumentBlock.DisplayFormula(Disp(Eq(F.Id("b"), Call("mul", F.Id("a"), Call("inv", Call("innerLift", P, F.Id("q"))))))),
                    Paragraph(Text("The resulting automorphism b belongs to B and has the same relative outer class as a. Thus the full outer kernel lies in the image of B under the relative quotient map, and is a p-group. Passing to H takes a subgroup of that kernel. No lift of a group extension or compatible choice of conjugators is assumed: only the individual quotient representative is lifted."))),
                DescribeRole.Theorem))));
}
