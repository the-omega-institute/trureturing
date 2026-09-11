using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class ConditionalPolynomialRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional closure under partial derivatives forces a polynomial subspace to depend on one linear form.",
        H("Conditional Polynomial Rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("conditional-polynomial-rigidity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/ConditionalPolynomialRigidity.conditional_derivative_closed_subspace_rigidity"),
                H("A shared linear form"),
                StatementSource.FromAuthor(RigidityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let K be any field of characteristic zero and sigma any finite type. " +
                        "Let L be a finite-dimensional K-linear subspace of the polynomial ring " +
                        "in variables indexed by sigma. Suppose the only constant polynomial in " +
                        "L is zero, and whenever p belongs to L and its constant coefficient " +
                        "vanishes, every partial derivative of p also belongs to L. If the " +
                        "dimension of L is at least two, there is one nonzero function c from " +
                        "sigma to K such that every p in L equals F(ell) for some univariate " +
                        "polynomial F over K, where ell is the sum of c(i) times X(i). " +
                        "The same c works for all p; F may depend on p.")),
                    Paragraph(Text(
                        "Evaluation at zero is a linear map from L to the one-dimensional " +
                        "space K. The dimension assumption gives a nonzero element in its " +
                        "kernel. Choose a nonzero p in L of minimum total degree m. Its " +
                        "constant coefficient is nonzero: otherwise conditional closure puts " +
                        "every partial derivative in L, and a nonzero partial has strictly " +
                        "smaller total degree. All partials would therefore vanish. In " +
                        "characteristic zero this makes p constant, and its zero constant " +
                        "coefficient would make p zero.")),
                    Paragraph(Text(
                        "Choose a nonzero q of least total degree n in the evaluation kernel. " +
                        "Some partial derivative of q is nonzero, so minimality of p gives " +
                        "m less than n. For any r in L of degree less than n, subtract " +
                        "r(0)/p(0) times p. This difference still has degree less than n " +
                        "and has zero evaluation; minimality of q makes it zero. Hence each " +
                        "partial derivative of q equals c(i) times p, with some c(i) nonzero. " +
                        "Commuting mixed partials gives c(j) times partial_i p equals c(i) " +
                        "times partial_j p. Polynomial tangent descent then gives p in K[ell].")),
                    Paragraph(Text(
                        "Suppose L has an element outside K[ell], and choose one, h, of " +
                        "minimum total degree. Set g equal to h minus h(0)/p(0) times p. " +
                        "Then g lies in L, has zero constant coefficient, remains outside " +
                        "K[ell], and has degree no greater than that of h. Each partial " +
                        "derivative of g lies in L and has smaller degree when nonzero, " +
                        "so each lies in K[ell].")),
                    Paragraph(Text(
                        "Fix indices i and j. The polynomial c(j) times partial_i g minus " +
                        "c(i) times partial_j g belongs to L by conditional closure. " +
                        "Every partial derivative of this polynomial is zero: commute " +
                        "mixed partials and use tangent descent on each partial of g, " +
                        "which already lies in K[ell]. It is therefore constant, and " +
                        "the exclusion of nonzero constants from L makes it zero. " +
                        "Tangent descent now puts g in K[ell], a contradiction. Thus " +
                        "L is contained in K[ell], and membership in this subalgebra " +
                        "gives the required univariate representation.")),
                    Paragraph(Text(
                        "Products by elements of K denote scalar actions. Individual " +
                        "coefficients c(i) may vanish, and no order or positivity is assumed. " +
                        "No additional nonemptiness assumption is imposed on sigma. " +
                        "The conclusion is containment in K[ell]; the subspace L need " +
                        "not be an algebra and contains no nonzero constant."))),
                DescribeRole.Theorem))));

    private static Formula RigidityFormula()
    {
        Formula field = F.Id("K");
        Formula variables = F.Id("sigma");
        Formula subspace = F.Id("L");
        Formula p = F.Id("p");
        Formula a = F.Id("a");
        Formula i = F.Id("i");
        Formula c = F.Id("c");
        Formula polynomial = F.Id("F");
        Formula ring = Call("MvPolynomial", variables, field);
        Formula excludesConstants = Seq(
            Forall, Sp, a, Colon, Sp, field, Comma, Sp,
            Call("C", a), Sp, InMacro, Sp, subspace, Sp, Implies, Sp,
            a, Sp, Eq, Sp, D(0));
        Formula conditionalClosure = Seq(
            Forall, Sp, p, Sp, InMacro, Sp, subspace, Comma, Sp,
            Call("constantCoeff", p), Sp, Eq, Sp, D(0), Sp, Implies, Sp,
            Forall, Sp, i, Sp, InMacro, Sp, variables, Comma, Sp,
            Call("pderiv", i, p), Sp, InMacro, Sp, subspace);
        Formula linearForm = Seq(
            Sum, Underscore, Grp(Seq(i, Sp, InMacro, Sp, variables)), Sp,
            c, Open, i, Close, Sp, Cdot, Sp, F.Id("X"), Underscore, Grp(i));
        Formula conclusion = Seq(
            Exists, Sp, c, Colon, Sp, variables, Sp, To, Sp, field, Comma, Sp,
            c, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            Open, Forall, Sp, p, Sp, InMacro, Sp, subspace, Comma, Sp,
            Exists, Sp, polynomial, Colon, Sp, Call("Polynomial", field), Comma, Sp,
            p, Sp, Eq, Sp, Call("aeval", linearForm, polynomial), Close);

        return Disp(Seq(
            Forall, Sp, field, Comma, Sp, variables, Colon, Sp, F.Id("Type"), Comma, Sp,
            Call("Field", field), Comma, Sp, Call("CharZero", field), Comma, Sp,
            Call("Fintype", variables), Comma, Esc,
            Forall, Sp, subspace, Colon, Sp, Call("Submodule", field, ring), Comma, Sp,
            Call("FiniteDimensional", field, subspace), Comma, Esc,
            Open, excludesConstants, Close, Sp, Implies, Esc,
            Open, conditionalClosure, Close, Sp, Implies, Esc,
            D(2), Sp, Leq, Sp, Call("finrank", field, subspace), Sp, Implies, Esc,
            conclusion, Dot));
    }
}
