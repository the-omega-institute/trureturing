using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using SF = StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismFormula;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal static class EvolutionAutomorphismFormula
{
    internal static Formula V(string s) => F.Id(s);
    internal static Formula Call(string s, params Formula[] a) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(s))), [.. a]);
    internal static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    internal static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    internal static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    internal static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    internal static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    internal static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    internal static Formula Type => V("Typeu");
    internal static Formula Rel(Formula v) => new Formula.TypeArrow(v, new Formula.TypeArrow(v, V("Prop")));
    internal static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    internal static Formula Card(Formula t) => Call("card", t);
    internal static Formula Blocks(Formula r) => Call("Blocks", r);
    internal static Formula Out(Formula r) => Call("PositiveOutdegree", r);
    internal static Formula In(Formula r) => Call("PositiveIndegree", r);
    internal static DocumentBlock.Describe Desc(string module, string name, string title,
        Formula f, string text, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/FiniteGroups/" + module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(),
            StrataLint.Scribe.DefinitionDsl.Blocks(Paragraph(Text(text))), role);
}


internal sealed class EvolutionAutomorphismControlDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.";
    private static Formula N => SF.V("n");
    private static Formula Mu => SF.V("mu");
    private static Formula B => SF.V("b");
    private static Formula R => SF.Call("supportRelation",Mu,B);
    private static Formula Beta => SF.Call("beta",R);
    private static Formula Aut => SF.Call("Aut",Mu);
    private static Formula Context(Formula f) => SF.All("n",SF.Call("NaturalNumbers"),
        SF.All("mu",SF.Call("Product",N),
            SF.All("b",SF.Call("Basis",SF.Call("Fin",N),SF.Call("Complex"),SF.Call("Coord",N)),
                SF.Imp(SF.Call("NaturalBasisAt",Mu,B),SF.Imp(SF.Call("perfect",Mu),f)))));
    private static DocumentBlock.Describe Desc(string name,string title,Formula f,string text,
        DescribeRole role=DescribeRole.Theorem,bool literature=false) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),DeclarationHandle.Create(Prefix+name),H(title),
            StatementSource.FromAuthor(Disp(f)),literature ? AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/QuadraticForms/kaygorodov2026evolution")) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full multiplication-preserving linear group of a perfect evolution product is finite and obeys a joint successor-quotient bound.",
        H("Algebra automorphisms and the canonical support quotient"), Blocks(
            Paragraph(Text("For the coordinate estimates the space is Coord(n)=Fin(n) to the complex numbers. The multiplication is a bilinear map, with no associativity or unit assumption. "
                + "NaturalBasisAt(mu,b) means mu(b(i),b(j))=0 whenever i differs from j. Perfectness means all pair products span the coordinate space. "
                + "The support relation has an arrow i to j exactly when the j-coordinate of mu(b(i),b(i)) in b is nonzero; loops are retained.")),
            Desc("Aut","All multiplication automorphisms",
                SF.All("A",SF.Type,SF.Imp(SF.Call("ComplexVectorSpace",SF.V("A")),
                    SF.All("mu",SF.Call("BilinearProduct",SF.V("A")),
                        SF.Eq(Aut,SF.Call("MultiplicationPreservingLinearEquivs",Mu))))),
                "Aut(mu) is the subgroup of all invertible complex-linear maps f with f(mu(x,y))=mu(f(x),f(y)) for every pair x,y. "
                + "Membership assumes neither monomiality nor graph data nor finiteness.",DescribeRole.Definition),
            Desc("rho","The actual support permutation homomorphism",
                Context(SF.Call("MonoidHom",Aut,SF.Call("Perm",SF.Call("Fin",N)))),
                "Square-vector independence follows from perfectness and the original natural_basis_structure_map. For distinct basis vectors, "
                + "their image product is zero. Injectivity of that structure map forces every matrix row to contain at most one nonzero entry. "
                + "Invertibility supplies exactly one in every row and column. Thus each actual automorphism has a unique basis-image permutation. "
                + "Comparing coefficients shows that this permutation preserves support, and uniqueness makes rho multiplicative. "
                + "Monomiality is a credited supporting result from the survey, consumed here to build the full group bound.",DescribeRole.Definition,true),
            Desc("kernelAssignmentEquiv","The exact diagonal kernel",
                Context(SF.Call("Equiv",SF.Call("ker",SF.Call("rho",Mu,B)),
                    SF.Call("Assignments",R,SF.V("UnitSquaring")))),
                "UnitSquaring is z mapped to z squared on the nonzero complex units. The kernel consists exactly of diagonal automorphisms "
                + "with t(j)=t(i)^2 on every support arrow. The forward map uses the actual kernel; the inverse constructs an invertible diagonal "
                + "linear map and proves multiplication preservation from these equations on basis pairs. Thus every assignment is realized, "
                + "without assuming that arbitrary graph automorphisms lift.",DescribeRole.Definition,literature:true),
            Desc("diagonal_kernel_card","The exact diagonal cycle cardinality",
                Context(SF.Eq(SF.Card(SF.Call("ker",SF.Call("rho",Mu,B))),SF.Call("cycleWeight",Beta))),
                "The entire diagonal kernel is equivalent to the support-arrow assignments, which descend bijectively to the least quotient. "
                + "Evaluation and independent realization identify its assignments with one roots-of-unity group per successor cycle. "
                + "Consequently its cardinality equals cycleWeight(beta), including the neutral singleton factors."),
            Desc("automorphism_finite","Actual finiteness",
                Context(SF.Call("Finite",Aut)),
                "Perfectness gives positive in- and outdegree. Diagonal assignments descend exactly through the least admissible support quotient. "
                + "Its successor beta is a finite permutation; a common return time puts every coordinate in a finite roots-of-unity group. "
                + "The permutation kernel and image are finite, hence so is the original algebra group. Natural cardinality is used only after this step.",literature:true),
            Desc("automorphism_quotient_bound","The joint algebraic quotient bound",
                Context(SF.Le(SF.Card(Aut),SF.Mul(SF.Mul(SF.Call("cycleWeight",Beta),
                    SF.Card(SF.Call("centralizer",Beta))),SF.Call("BlockFactorialProduct",R)))),
                "Let P be Blocks(R), beta its successor, and Fiber(R,q) the actual vertices in class q. BlockFactorialProduct is the product over q in P "
                + "of factorial(card(Fiber(R,q))). The centralizer is taken in the symmetric group on P. cycleWeight(beta) is the product of "
                + "2^l-1 over all its cycles, including the factor one on fixed points. These cycles partition P, whose size can be smaller than n. "
                + "The actual algebra group maps into the support automorphism group. Both the diagonal-root bound and the quotient-action bound apply "
                + "to that same group. The block-action kernel is retained through its injection into the product of the actual block symmetric groups. "
                + "No faithful quotient action or support-surjectivity assumption is made."),
            Paragraph(Text("This coordinate theorem is the algebraic core of the arbitrary-module bound toward Conjecture 3 of Kaygorodov, Martín González and Viruel, arXiv:2610.22248v1. "
                + "It establishes a joint upper bound, not the sharp all-dimensional maximum. The universal partition estimate, six small values, factorial tail, "
                + "cycle-family attainment and final maximum assembly remain separate statements. "
                + "EvolutionBasisTransport conjugates the entire group on an arbitrary complex module to this coordinate model. "
                + "The diagonal root count is an equality: cycle evaluation has an independently constructed inverse."))), []));
}
