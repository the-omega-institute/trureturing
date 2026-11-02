using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class FrattiniAutomorphismKernelDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/cfsg2026frattinikernel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Automorphisms of a finite prime-power group acting trivially on its Frattini quotient form a prime-power group.",
        H("The Ordinary Frattini Automorphism Kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("characteristic-quotient-action"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/FrattiniAutomorphismKernel.quotientAut"),
                H("The action on a characteristic quotient"),
                StatementSource.FromAuthor(QuotientAction()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a characteristic subgroup C of a group G, quotientAut C sends an "
                    + "automorphism a to the induced automorphism of G/C. On a coset represented "
                    + "by g its value is the coset represented by a(g). The construction is a "
                    + "homomorphism, with multiplication given by composition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ordinary-frattini-kernel"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/FrattiniAutomorphismKernel.isPGroup_quotientAut_frattini_kernel"),
                H("The kernel is a prime-power group"),
                StatementSource.FromAuthor(KernelTheorem()), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let G be any finite group and let p be a natural number. If every element "
                        + "of G has order dividing a power of p, the same holds for the kernel of "
                        + "Aut(G) to Aut(G/Frattini(G)). In particular this holds for every finite "
                        + "p-group with p prime, including the trivial group. No nontriviality, "
                        + "splitting, coprimality or extra automorphism hypothesis is imposed.")),
                    Paragraph(Text(
                        "Write C for Frattini(G) and K for this kernel. Consider all functions "
                        + "f from G to C, interpreted as the ordered family g f(g). For a in K "
                        + "the action sends f(g) to g inverse times a(g f(g)). This belongs to C "
                        + "because a acts trivially modulo C and preserves C.")),
                    Paragraph(Text(
                        "An automorphism stabilizing such a family fixes every g f(g). Its "
                        + "equalizer subgroup E with the identity satisfies E join C equal to G: "
                        + "multiply the fixed element g f(g) by f(g) inverse to obtain g. The "
                        + "nongenerating property of the Frattini subgroup forces E to be G. "
                        + "Thus every stabilizer is trivial.")),
                    Paragraph(Text(
                        "Orbit decomposition identifies the function space with its orbit "
                        + "quotient times K. Hence the order of K divides the number of functions, "
                        + "which is the order of C raised to the order of G. Since C is a subgroup "
                        + "of the given p-group, this cardinality divides a power of p.")),
                    Paragraph(Text(
                        "This is the ordinary automorphism-kernel statement. It does not assert "
                        + "the commutator-and-powers formula for the Frattini subgroup, nor the "
                        + "relative or outer-automorphism kernel theorem for a normal subgroup "
                        + "of a larger finite group."))),
                DescribeRole.Theorem))));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula BaseGroup(Formula body) =>
        All("G", F.Id("Type"), All("group", Call("Group", F.Id("G")), body));
    private static Formula QuotientAction()
    {
        var g = F.Id("g"); var a = F.Id("a"); var c = F.Id("C");
        return Disp(BaseGroup(All("C", Call("Subgroup", F.Id("G")),
            All("characteristic", Call("Characteristic", c),
            All("a", Call("MulAut", F.Id("G")), All("g", F.Id("G"),
                new Formula.Relation(
                    Call("quotientAut", c, a, Call("coset", g, c)),
                    FormulaRelationOperator.Equal, Call("coset", Call("apply", a, g), c))))))));
    }
    private static Formula KernelTheorem()
    {
        var g = F.Id("G"); var p = F.Id("p");
        return Disp(BaseGroup(All("finite", Call("Finite", g),
            All("p", Seq(Mathbb, Grp(F.Id("N"))), new Formula.Logic(
                Call("IsPGroup", p, g), FormulaLogicOperator.Implies,
                Call("IsPGroup", p, Call("ker", Call("quotientAut", Call("frattini", g)))))))));
    }

}
