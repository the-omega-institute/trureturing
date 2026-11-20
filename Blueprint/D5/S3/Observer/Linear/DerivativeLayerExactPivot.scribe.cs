using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class DerivativeLayerExactPivotDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact Schur pivot for derivative layers", H("Exact Schur pivot for derivative layers"), Blocks(
            Describe.Lean(DescribeId.Create("filtered-polynomial-pivot-is-least"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/DerivativeLayerExactPivot.filtered_polynomial_pivot_isLeast"),
                H("Attained minimum for filtered vector polynomials"), StatementSource.FromAuthor(Filtered()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let W be a real inner-product space, X(i) any family of real modules, and D(i) : X(i) → W linear. If v belongs to the range of every D(i) with i < k, the squared L² distance on [0,1] from sᵏv to the polynomials with those lower-degree coefficients has an attained minimum of ‖v‖² divided by the product of (2k+1) and the square of the binomial coefficient (2k choose k).")),
                    Paragraph(Text("The monic shifted Legendre polynomial p of degree k is orthogonal to every scalar monomial of degree below k. The residual p(s)v is therefore orthogonal to every allowed vector polynomial of lower degree. Its squared norm is the stated minimum. The coefficient of degree i in the projection is −coeff(p,i)v. Each such coefficient has a preimage in X(i), and these preimages attain the minimum.")),
                    Paragraph(Text("At k=0 the family of trial coefficients is empty and the minimum is ‖v‖². If v=0 the minimum is zero. Neither finite dimension nor completeness of W is required."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("derivative-layer-pivot-is-least"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/DerivativeLayerExactPivot.derivative_layer_pivot_isLeast"),
                H("Exact minimum for the factorially normalized derivative layer"), StatementSource.FromAuthor(Derivative()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For a finite-dimensional real inner-product state space V, arbitrary real inner-product output space W, and linear maps B : V → V and C : V → W, let N(k) be the intersection of the kernels of CBʲ for j < k and E(k) = N(k) ∩ N(k+1)⊥. The actual degree-k output map D(k) on E(k) is CBᵏ divided by k!. Its range equals CBᵏ(N(k)). Applying B takes N(k+1) into N(k), so these output ranges are nested.")),
                    Paragraph(Text("For any x in E(k), take v = D(k)x in the attained polynomial minimum. Every trial coefficient of degree i comes from an independent state in E(i) through CBⁱ divided by i!. The result retains zero-dimensional spaces, zero layers and repeated output ranges. With the unnormalized vector CBᵏx, the minimum includes the additional factor 1/(k!)².")),
                    Paragraph(Text("In the normalized polynomial Gramian this minimum gives the quadratic form of the degree-k Schur complement after eliminating the earlier layers. On the observable state space, the ordinary spectral proof passes the O(T) error in the positive normalized Gramian through block elimination to the Schur blocks. When the block triangular factor is conjugated by the time scaling, a strict lower block in row j and column i acquires the factor T^(j−i). The resulting factor is I+O(T). Min–max comparison gives dim E(k) decreasing eigenvalues at the scale T^(2k+1), with leading coefficients from that limiting Schur block, counted with multiplicity and with relative O(T) error for fixed B and C. This transfer to the sorted spectrum is a separate ordinary proof."))),
                DescribeRole.Theorem))));

    private static Formula Filtered()
    {
        Formula w = F.Id("W"), x = F.Id("X"), d = F.Id("D"), i = F.Id("i");
        Formula k = F.Id("k"), v = F.Id("v"), a = F.Id("a");
        Formula xi = App(x, i), di = App(d, i);
        return Disp(Seq(Begin, Grp(F.Id("gathered")),
            Forall, Sp, w, Comma, Sp, Instance("RealInnerProductSpace", w), Comma, Sp,
            Forall, Sp, x, Colon, Sp, Naturals, Sp, To, Sp, F.Id("Type"), Comma, Sp,
            Instance("RealModuleFamily", x), Comma, RowBreak,
            Forall, Sp, d, Colon, Sp, Product(i, Naturals, Call("RealLinear", xi, w)), Comma, Sp,
            Forall, Sp, k, Colon, Sp, Naturals, Comma, Sp,
            Forall, Sp, v, Colon, Sp, w, Comma, RowBreak,
            Open, Forall, Sp, i, InMacro, Sp, Call("Fin", k), Comma, Sp,
            v, InMacro, Sp, Call("range", di), Close, Sp, Rightarrow, RowBreak,
            Minimum(k, v, i, a, xi, App(di, App(a, i))),
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Derivative()
    {
        Formula v = F.Id("V"), w = F.Id("W"), b = F.Id("B"), c = F.Id("C");
        Formula i = F.Id("i"), k = F.Id("k"), x = F.Id("x"), a = F.Id("a");
        Formula layer = App(F.Id("E"), b, c);
        Formula output = App(F.Id("D"), b, c);
        return Disp(Seq(Begin, Grp(F.Id("gathered")),
            Forall, Sp, v, Comma, Sp, w, Comma, Sp, Instance("RealInnerProductSpace", v),
            Sp, Instance("FiniteDimensional", v), Sp, Instance("RealInnerProductSpace", w), Comma, RowBreak,
            Forall, Sp, b, Colon, Sp, Call("RealLinear", v, v), Comma, Sp,
            Forall, Sp, c, Colon, Sp, Call("RealLinear", v, w), Comma, Sp,
            Forall, Sp, k, Colon, Sp, Naturals, Comma, Sp,
            Forall, Sp, x, Colon, Sp, App(layer, k), Comma, RowBreak,
            Minimum(k, App(output, k, x), i, a, App(layer, i), App(output, i, App(a, i))),
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Minimum(Formula k, Formula v, Formula i, Formula a,
        Formula coefficientSpace, Formula coefficient)
    {
        Formula s = F.Id("s");
        Formula coefficients = Product(i, Call("Fin", k), coefficientSpace);
        Formula sum = Seq(Sum, Underscore, Grp(i, InMacro, Sp, Call("Fin", k)),
            Sp, Pow(s, i), Cdot, Sp, coefficient);
        Formula energy = Seq(Int, Underscore, Grp(D(0)), Caret, Grp(D(1)), Sp,
            NormSquared(Seq(Pow(s, k), Cdot, Sp, v, Minus, sum)), Sp, Mathrm, Grp(F.Id("d")), s);
        Formula values = Seq(OpenBrace, energy, Sp, Mid, Sp, a, Colon, Sp, coefficients, CloseBrace);
        Formula factor = Seq(Frac, Grp(D(1)), Grp(Open, D(2), k, Plus, D(1), Close,
            Pow(Call("choose", Seq(D(2), k), k), D(2))));
        return Call("IsLeast", values, Seq(factor, Sp, NormSquared(v)));
    }

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Pow(Formula value, Formula exponent) => Seq(value, Caret, Grp(exponent));
    private static Formula NormSquared(Formula value) => Pow(new Formula.Norm(value), D(2));
    private static Formula Product(Formula index, Formula domain, Formula body) =>
        Seq(Prod, Underscore, Grp(index, Colon, Sp, domain), Sp, body);
    private static Formula Instance(string name, Formula space) => Seq(OpenBracket, Call(name, space), CloseBracket);
    private static Formula Call(string name, params Formula[] arguments) =>
        App(Seq(Operatorname, Grp(F.Id(name))), arguments);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
}
