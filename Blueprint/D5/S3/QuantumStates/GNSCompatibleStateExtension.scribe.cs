using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumStates;

internal sealed class GNSCompatibleStateExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatible local C-star states on a dense increasing union and their completed GNS representation.",
        H("Compatible states and normalized cyclic GNS expectations"),
        Blocks(Describe.Lean(DescribeId.Create("compatible-state-extension"),
            DeclarationHandle.Create("D5/S3/QuantumStates/GNSCompatibleStateExtension.compatible_state_extension"),
            H("Unique continuous extension with normalized cyclic representation"),
            StatementSource.FromAuthor(Disp(All("A",Call("Type"),Instance(Call("CstarAlgebra",F.Id("A")),Instance(Call("PartialOrder",F.Id("A")),Instance(Call("StarOrderedRing",F.Id("A")),All("S",Call("Function",Call("Nat"),Call("StarSubalgebra",Call("Complex"),F.Id("A"))),All("omega",Call("DependentPositiveFunctionals",F.Id("S")),Rel(Conj(Call("Monotone",F.Id("S")),All("n",Call("Nat"),Conj(Call("Closed",Call("Apply",F.Id("S"),F.Id("n"))),Call("InheritedStarOrder",Call("Apply",F.Id("S"),F.Id("n"))),Rel(Call("Apply",F.Id("omega"),F.Id("n"),D(1)),Eq,D(1)))),All("n",Call("Nat"),All("m",Call("Nat"),All("a",Call("Apply",F.Id("S"),F.Id("n")),Rel(Rel(F.Id("n"),Le,F.Id("m")),Implies,Rel(Call("Apply",F.Id("omega"),F.Id("m"),Call("Include",F.Id("n"),F.Id("m"),F.Id("a"))),Eq,Call("Apply",F.Id("omega"),F.Id("n"),F.Id("a"))))))),Call("DenseUnion",F.Id("S"),F.Id("A"))),Implies,Unique("f",Call("PositiveLinearFunctional",F.Id("A")),Conj(Rel(Call("Apply",F.Id("f"),D(1)),Eq,D(1)),All("n",Call("Nat"),All("a",Call("Apply",F.Id("S"),F.Id("n")),Rel(Call("Apply",F.Id("f"),F.Id("a")),Eq,Call("Apply",F.Id("omega"),F.Id("n"),F.Id("a"))))),All("a",F.Id("A"),Rel(Call("Norm",Call("Apply",F.Id("f"),F.Id("a"))),Le,Call("Norm",F.Id("a")))),Rel(Call("Norm",Call("cyclicVector",F.Id("f"))),Eq,D(1)),All("a",F.Id("A"),Rel(Call("Inner",Call("cyclicVector",F.Id("f")),Call("Apply",Call("gnsStarAlgHom",F.Id("f")),F.Id("a"),Call("cyclicVector",F.Id("f")))),Eq,Call("Apply",F.Id("f"),F.Id("a")))),Call("DenseOrbit",Call("gnsStarAlgHom",F.Id("f")),Call("cyclicVector",F.Id("f")))))))))))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/fewsterrejzner2019algebraicqft")),
            Blocks(
                Paragraph(Text("Let A be a unital C-star algebra, and let S(n) be increasing closed unital star subalgebras whose union is dense in A. Each S(n) has the inherited star order, and omega(n) is a positive complex-linear functional normalized at the common unit. Compatibility means that inclusion from S(n) to S(m), for n<=m, preserves omega(n). Finite-dimensional local algebras are closed by Submodule.closed_of_finiteDimensional. In a closed star subalgebra, functional calculus retains the ambient positive square root; its square equals the positive element. Hence the inherited order is a star order. Both interface obligations are constructed in the finite-local exact application, rather than added as independent hypotheses. Taking A to be the norm closure of the algebraic union supplies the density condition.")),
                Paragraph(Text("Positivity gives Cauchy-Schwarz in the pre-GNS carrier. Together with the bound on omega(a* a), normalization implies |omega(a)|<=norm(a). On the directed union choose a stage containing a. Compatibility makes its value independent of the stage; a common maximum stage proves additivity and complex linearity. LinearMap.extendOfNorm extends this contractive functional to A. Its values on a* a remain nonnegative by continuity and density. Every positive element of a C-star algebra is a square of this form, so the extension is positive. A continuous positive functional agreeing on the dense union is equal to this extension.")),
                Paragraph(Text("For the resulting normalized functional f, use the pinned Mathlib PositiveLinearMap.PreGNS quotient, completion GNS, and representation gnsStarAlgHom. The null ideal and bounded left multiplication are supplied by Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal; they are not extra axioms. Omega is the completion image of f.toPreGNS(1). Its norm is one, and the completed expectation inner(Omega,pi(a)Omega) equals f(a). Left multiplication sends Omega to the image of f.toPreGNS(a). The quotient map is surjective and the completion image is dense, so this orbit is cyclic. The theorem concerns this exact completed Hilbert space and this exact extension.")),
                Paragraph(Text("A nonzero equal coefficient on every finite word cannot be square summable. The words consisting of n repetitions of one fixed letter form an injective sequence. Summability on all words would give summability of the same positive constant along this sequence, contradicting infinitude. Hence finite normalized equal-weight history vectors cannot be extended by placing an infinite clock directly in ell2. This is a compiled application of Memlp and the constant-summability boundary, not an additional state assumption."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Unique(string name, Formula type, Formula body) =>
        Seq(Open, Exists, Sp, Bang, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Rel(Formula left, Formula relation, Formula right) =>
        Seq(Open, left, Sp, relation, Sp, right, Close);
    private static Formula Conj(params Formula[] statements) =>
        statements.Aggregate((left, right) => Rel(left, Land, right));
    private static Formula Instance(Formula instance, Formula body) =>
        Seq(OpenBracket, instance, CloseBracket, Sp, body);
}
