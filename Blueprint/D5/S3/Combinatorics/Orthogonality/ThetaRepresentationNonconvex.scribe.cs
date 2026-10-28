using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;

internal sealed class ThetaRepresentationNonconvexDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Orthogonality/ThetaRepresentationNonconvex.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/carlisilva2026kfoldtheta");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The five-cycle has a nonconvex trace-two orthonormal representation set.",
        H("Nonconvexity of the theta representation set"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dot-cauchy"),
                DeclarationHandle.Create(Prefix + "dot_cauchy"),
                H("Cauchy-Schwarz for finite real vectors"),
                StatementSource.FromAuthor(DotCauchyFormula()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuadraticForms/mathlib2026finitecauchyschwarz")),
                Blocks(Paragraph(Text(
                    "For real vectors indexed by any finite type, the square of their dot "
                    + "product is at most the product of their squared lengths."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("theta-representation-set"),
                DeclarationHandle.Create(Prefix + "representationSet"),
                H("The full orthonormal representation set"),
                StatementSource.FromAuthor(RepresentationFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Section 5.3, proof of Theorem 16, defines M_k(G). The finite vertex "
                    + "type V indexes both vector coordinates and matrix rows and columns. "
                    + "All coordinates of x use the same real matrix M and the same family u. "
                    + "M and I-M are positive semidefinite, and tr(M)=k exactly. "
                    + "PosSemidef includes the real symmetry condition. Each u_i is a unit "
                    + "vector; orthogonality is required on every edge of G. This is the "
                    + "source's orthonormal representation of the complement of G. "
                    + "There is no orthogonality condition on nonedges, no rank constraint, "
                    + "and no requirement that M be a projector. The real dot product on "
                    + "V->R is the standard Euclidean inner product in dimension |V|."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("theta-convexity-assertion"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The universal affirmative convexity assertion"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Section 7 item (iv) asks: Is the orthonormal representation set M_k(G) "
                    + "convex? The affirmative assertion quantifies over every finite "
                    + "nonempty vertex type, every ordinary simple graph, and every real "
                    + "k with 0<k<=|V|. Convexity means closure under all real convex "
                    + "combinations, with both points, both nonnegative coefficients, and "
                    + "their sum-one condition quantified. DecidableEq is supplied "
                    + "classically on every finite vertex type and adds no graph restriction. "
                    + "The upper bound on k is feasibility of the matrix constraints. "
                    + "The source's separate question about the closed convex lower hull "
                    + "is outside this assertion."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("theta-convexity-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The five-cycle refutes convexity"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Call("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Label the five-cycle by 0,1,2,3,4, with edges 01,12,23,34,40. "
                        + "The points a=(0,1,1,1,1), b=(1,0,1,1,1), c=(1,1,0,1,1) "
                        + "belong to M_2(C_5). Use M=diag(1,1,0,0,0) and coordinate vectors "
                        + "e_0,e_1,e_2 in R^5. The vector families for a,b,c respectively "
                        + "are (e_2,e_0,e_1,e_0,e_1), (e_1,e_2,e_0,e_1,e_0), and "
                        + "(e_0,e_1,e_2,e_0,e_1). Every edge has orthogonal vectors. "
                        + "Their equal average is t=(2/3,2/3,2/3,1,1).")),
                    Paragraph(Text(
                        "Suppose any allowed M and u realize t. Write A=u_3 and B=u_4. "
                        + "These are orthogonal unit vectors. Since the quadratic forms "
                        + "of I-M vanish at A and B, positivity implies MA=A and MB=B. "
                        + "Set P=AA^T+BB^T. For any w, subtract its A and B components "
                        + "to obtain r(w). Expansion gives w^T(M-P)w=r(w)^T M r(w)>=0. "
                        + "Thus M-P is positive semidefinite. Its trace is 2-1-1=0, "
                        + "so the positive semidefinite trace-zero theorem gives M=P. "
                        + "This derives the projection from the full contraction domain.")),
                    Paragraph(Text(
                        "Let alpha=A dot u_0, beta=B dot u_2, p=A dot u_1, and q=B dot u_1. "
                        + "Edges 40 and 23 give B dot u_0=0 and A dot u_2=0. Hence "
                        + "alpha^2=beta^2=2/3 and p^2+q^2=2/3. The three residuals "
                        + "r(u_0),r(u_1),r(u_2) each have squared length 1/3. "
                        + "Edges 01 and 12 give residual inner products -alpha p and "
                        + "-beta q. Cauchy-Schwarz therefore yields (2/3)p^2<=1/9 "
                        + "and (2/3)q^2<=1/9, or p^2,q^2<=1/6. Their sum is at most "
                        + "1/3, contradicting 2/3. This excludes every possible realization.")),
                    Paragraph(Text(
                        "If M_2(C_5) were convex, first averaging b and c with coefficients "
                        + "1/2,1/2 and then combining a and that average with 1/3,2/3 "
                        + "would put t in the set. Its exclusion proves nonconvexity. "
                        + "The counterexample uses k=2>1 and |V|=5. No characterization "
                        + "of the closed convex lower hull follows from this theorem."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("carli-silva-2026-theta-representation-convexity-clause"),
                    ResolutionKind.Refuted))),
        []));

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Instance(Formula domain, Formula body) =>
        Seq(OpenBracket, domain, CloseBracket, Comma, Sp, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FiniteVertex(Formula body) => All("V", Call("Type"),
        Instance(Call("Fintype", F.Id("V")), Instance(Call("DecidableEq", F.Id("V")), body)));

    private static Formula DotCauchyFormula()
    {
        Formula v = F.Id("v"), w = F.Id("w"), coordinates = F.Id("V");
        Formula vectors = Arrow(coordinates, Real());
        Formula bound = Le(new Formula.Power(Call("dotProduct", v, w), D(2)),
            new Formula.Binary(Call("dotProduct", v, v), FormulaBinaryOperator.Multiply,
                Call("dotProduct", w, w)));
        return Disp(All("V", Call("Type"), Instance(Call("Fintype", coordinates),
            All("v", vectors, All("w", vectors, bound)))));
    }

    private static Formula RepresentationFormula()
    {
        Formula v = F.Id("V"), g = F.Id("G"), k = F.Id("k"), x = F.Id("x");
        Formula m = F.Id("M"), u = F.Id("u"), i = F.Id("i"), j = F.Id("j");
        Formula ui = App(u, i), uj = App(u, j);
        Formula vectors = Arrow(v, Real());
        Formula nonnegative = All("i", v, Le(D(0), App(x, i)));
        Formula unit = All("i", v, Eq(Call("dotProduct", ui, ui), D(1)));
        Formula orthogonal = All("i", v, All("j", v,
            Imp(Call("Adj", g, i, j), Eq(Call("dotProduct", ui, uj), D(0)))));
        Formula coordinates = All("i", v, Eq(App(x, i),
            Call("dotProduct", ui, Call("mulVec", m, ui))));
        Formula matrix = Exists("M", Call("Matrix", v, v, Real()),
            And(Call("PosSemidef", m),
                And(Call("PosSemidef", new Formula.Binary(D(1), FormulaBinaryOperator.Subtract, m)),
                    And(Eq(Call("trace", m), k),
                        Exists("u", Arrow(v, vectors), And(unit, And(orthogonal, coordinates)))))));
        Formula member = new Formula.Relation(x, FormulaRelationOperator.MemberOf,
            Call("representationSet", g, k));
        return Disp(FiniteVertex(All("G", Call("SimpleGraph", v), All("k", Real(),
            All("x", vectors, Iff(member, And(nonnegative, matrix)))))));
    }

    private static Formula ClaimFormula()
    {
        Formula v = F.Id("V"), g = F.Id("G"), k = F.Id("k");
        Formula card = Call("FintypeCard", v);
        return Disp(Iff(Call("claim"), FiniteVertex(Imp(Le(D(1), card),
            All("G", Call("SimpleGraph", v), All("k", Real(),
                Imp(Lt(D(0), k), Imp(Le(k, Call("NatCastReal", card)),
                    Call("Convex", Real(), Call("representationSet", g, k))))))))));
    }
}
