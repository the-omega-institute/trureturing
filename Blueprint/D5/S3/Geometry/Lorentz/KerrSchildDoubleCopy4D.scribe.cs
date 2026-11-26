using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class KerrSchildDoubleCopy4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.";
    private static LibraryNoteRef KerrSchild => LibraryNoteRef.Create("D5/L/LieTheory/monteiro2014kerrschild");
    private static LibraryNoteRef WeylCopy => LibraryNoteRef.Create("D5/L/LieTheory/luna2019weyldoublecopy");
    private static Formula K => F.Id("K");
    private static Formula P => F.Id("p");
    private static Formula V => F.Id("k");
    private static Formula J => F.Id("j");
    private static Formula I => F.Id("i");
    private static Formula B => F.Id("b");
    private static Formula A => F.Id("a");
    private static Formula R => F.Id("r");
    private static Formula S => F.Id("s");
    private static Formula T => F.Id("t");
    private static Formula Z => F.Id("D");
    private static Formula Index => Call("Fin", D(4));
    private static Formula Ray => Op("Ray");
    private static Formula Weyl => Seq(Op("Weyl"), Underscore, Grp(D(4)));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula EtaNorm => Call("n", V);
    private static Formula G => Call("g", P, V);
    private static Formula Inv => Call("ginv", P, V);
    private static Formula Q => Call("Q", A, R, S);
    private static Formula C => Call("C", A, R, S);
    private static Formula Zero => D(0);
    private static Formula One => D(1);
    private static Formula Two => D(2);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact curvature and projective double copies in four dimensions.",
        H("Kerr–Schild double copy in four dimensions"),
        Blocks(
            Paragraph(Text("Use Cartesian coordinates with η = diag(−1, 1, 1, 1). Write p for the scalar φ, "
                + "k for the lower covector, and n(k) for the contraction of k with its background-raised vector. "
                + "The metric g is η + p k ⊗ k and ginv is η − p k♯ ⊗ k♯.")),
            Node("metric-symmetry", "ks_metric_symm", "Metric symmetry",
                OverVectors(Equal(Seq(Parens(G), Caret, Grp(F.Id("T"))), G)),
                "Both the background and the outer product are symmetric."),
            Node("metric-inverse", "ks_metric_mul_inv", "Exact inverse",
                OverVectors(Implies(Equal(EtaNorm, Zero), And(Equal(Mul(G, Inv), One), Equal(Mul(Inv, G), One)))),
                "The cross terms cancel, and nullity kills the product of the two rank-one terms.", KerrSchild),
            Node("determinant-formula", "ks_metric_det_formula", "Rank-one determinant",
                OverVectors(Equal(Call("det", G), MinusOf(Parens(Plus(One, Mul(P, EtaNorm)))))),
                "Factor out η and apply the rank-one determinant identity."),
            Node("null-determinant", "ks_metric_det", "Determinant on the null cone",
                OverVectors(Implies(Equal(EtaNorm, Zero), Equal(Call("det", G), MinusOf(One)))),
                "The determinant is constant along every null rank-one update."),
            Paragraph(Text("For the unit lower time covector, n(k) = −1. The determinant is then −(1 − p), "
                + "which differs from −1 whenever p is nonzero.")),
            Paragraph(Text("A jet j contains p, k and their first and symmetric second derivatives. "
                + "N(j) imposes the nullity equation and its first two derivatives. "
                + "G(j) imposes affine geodesicity and its first derivative. A first jet contains the values and first derivatives. "
                + "Its conditions Nzero, Nfirst, and Gzero are nullity, differentiated nullity, and affine geodesicity, respectively. "
                + "With h = p k ⊗ k, L is the Christoffel symbol of the first kind raised by η. "
                + "Γ uses the same first-kind symbol raised by ginv. Its derivative applies the product rule to both factors. "
                + "The mixed Ricci tensor R uses ginv to raise the first index after taking the full Ricci contraction. "
                + "The linear expression Lin raises both contractions in the divergence of the first-kind symbol with η.")),
            Node("christoffel", "ks_christoffel_exact", "Exact Christoffel decomposition",
                OverFirstJet(true, All("a", Index, All("i", Index, All("b", Index,
                    Equal(Gamma(A, I, B), Plus(Call("L", J, A, I, B), Half(Mul(
                        Call("phi", J), Call("along", J), Call("raised", J, A),
                        Call("k", J, I), Call("k", J, B))))))))),
                "The derivative along k♯ is along(j) = k♯ · dp. The contraction of the first-kind symbol with k♯ yields the negative of this derivative times k ⊗ k divided by two."),
            Node("christoffel-trace", "ks_christoffel_trace_zero", "Vanishing connection trace",
                OverFirstJet(false, All("i", Index, Equal(Sum("a", Gamma(A, A, I)), Zero))),
                "The flat trace vanishes by differentiated nullity. In the inverse correction, the two terms from differentiating along the traced indices cancel by exchanging those indices. The remaining term is proportional to the null contraction."),
            Node("linear-ricci", "ks_mixed_ricci_linear_in_phi", "Exact mixed Ricci linearity",
                OverJet(true, All("i", Index, All("b", Index, Equal(Call("R", J, I, B), Call("Lin", J, I, B))))),
                "The divergence of the rank-one connection correction and the connection product leave a covariant term proportional to k ⊗ k. "
                + "Contracting the flat divergence with k♯ identifies its coefficient and shows that raising with ginv cancels it. "
                + "In indices Lin is half of ∂ⁱ∂ₐhᵃ_b + ∂_b∂ₐhⁱᵃ − ∂ᵃ∂ₐhⁱ_b.", KerrSchild),
            Node("nongeodesic", "ks_mixed_ricci_nongeodesic", "A null non-geodesic jet",
                OverK("Field", true, All("p", K, Implies(Ne(P, Zero), NonGeodesicFormula()))),
                "Take the jet Jbad of (1, (1 − t²)/(1 + t²), 2t/(1 + t²), 0) at zero and hold p constant. "
                + "The only nonzero derivatives are the time derivative of the second spatial component and the second time derivative of the first spatial component."),
            Paragraph(Text("S(j) means time independence through order two and k₀ = 1 with its first and second derivatives zero. "
                + "The potential is A = p k, its field strength is Fₐᵦ = ∂ₐAᵦ − ∂ᵦAₐ, and Max is ∂ₐFᵃⁱ. "
                + "Lap denotes the sum of the three spatial diagonal second derivatives of p.")),
            Node("maxwell-copy", "stationary_ks_ricci_maxwell_double_copy", "Stationary Maxwell copy",
                OverJet(true, Implies(Call("S", J), All("i", Index, And(
                    Equal(Call("R", J, I, Zero), Half(MinusOf(Call("Max", J, I)))),
                    Equivalent(Equal(Call("R", J, I, Zero), Zero), Equal(Call("Max", J, I), Zero)))))),
                "The mixed Ricci time column equals negative one half of the Maxwell divergence.", KerrSchild),
            Node("poisson-copy", "stationary_ks_ricci_poisson_zeroth_copy", "Stationary scalar copy",
                OverJet(true, Implies(Call("S", J), And(
                    Equal(Call("R", J, Zero, Zero), Half(Call("Lap", J))),
                    Equivalent(Equal(Call("R", J, Zero, Zero), Zero), Equal(Call("Lap", J), Zero))))),
                "The lower time component of the potential is p, and raising its time index contributes a minus sign.", KerrSchild),
            Paragraph(Text("Ray denotes the complex projective line in the two stereographic charts. "
                + "For a finite ray z use the affine factor X − z, and for infinity use the factor 1 of homogeneous degree one. "
                + "The product f of the two factors has homogeneous degree two. The Maxwell quadratic q is a f, "
                + "Q is its square, and C is the inverse Weyl quartic image of Q. "
                + "W(D) denotes the Weyl quartic of D, m is projective multiplicity in degree four, and Tide is the complex screen tide. "
                + "The symbol ev is projective quartic evaluation. At infinity the multiplicity is four minus the affine degree and evaluation uses the fourth coefficient.")),
            Node("petrov-double-copy", "petrov_type_d_double_copy_quartic", "The type D quartic square",
                PetrovFormula(),
                "The two factors square, and evaluation at a third ray is nonzero for the unit amplitude. "
                + "Every nonzero quartic with the two indicated double roots has the same two squared factors and a constant quotient. "
                + "A tide at the third ray fixes that constant.", WeylCopy),
            Node("radial-quartic", "coulomb_schwarzschild_quartic", "Coulomb and Schwarzschild principal directions",
                CoulombFormula(),
                "In the radial spin frame the two axial rays are zero and infinity. "
                + "For nonzero amplitude the quartic gives the algebraic Schwarzschild type D pattern. "
                + "The spacetime Weyl double copy also includes the scalar normalization relating the physical fields.", WeylCopy)),
        []));

    private static Formula NonGeodesicFormula()
    {
        Formula j = Call("Jbad", P);
        Formula r = Call("R", j, Zero, Zero);
        Formula l = Call("Lin", j, Zero, Zero);
        return And(Call("N", j), Seq(Neg, Sp, Call("G", j)),
            Equal(Subtract(r, l), Mul(Two, Square(P))), Ne(r, l));
    }

    private static Formula PetrovFormula()
    {
        Formula f = Call("f", R, S);
        Formula tide = Call("Tide", C, T);
        Formula sameTide = Equal(Call("Tide", Z, T), tide);
        Formula w = Call("W", Z);
        return All("a", Complex, All("r", Ray, All("s", Ray, All("t", Ray, Implies(
            And(Ne(A, Zero), Ne(R, S), Ne(T, R), Ne(T, S)), And(
                Equal(Q, Square(Call("q", A, R, S))),
                Equal(Call("m", R, Q), Two), Equal(Call("m", S, Q), Two), Ne(C, Zero),
                Equal(tide, Mul(Square(A), Call("ev", T, Square(f)))),
                All("D", Weyl, Implies(And(Ne(Z, Zero), Equal(Call("m", R, w), Two),
                    Equal(Call("m", S, w), Two), sameTide), Equal(Z, C)))))))));
    }

    private static Formula CoulombFormula()
    {
        Formula inf = Seq(Infty);
        Formula x = F.Id("X");
        return All("a", Complex, And(Equal(Call("q", A, Zero, inf), Mul(A, x)),
            Equal(Call("Q", A, Zero, inf), Mul(Square(A), Square(x))),
            Equal(Call("Tide", Call("C", A, Zero, inf), One), Square(A))));
    }

    private static Formula OverVectors(Formula body) => OverK("CommRing", false, All("p", K,
        All("k", Seq(K, Caret, Grp(D(4))), body)));

    private static Formula OverFirstJet(bool geodesic, Formula body)
    {
        Formula nullity = Call("Nzero", J);
        Formula derivative = Call("Nfirst", J);
        Formula conditions = geodesic ? And(nullity, derivative, Call("Gzero", J)) : And(nullity, derivative);
        return OverK("Field", false, All("j", Call("FirstJet", K), Implies(conditions, body)));
    }

    private static Formula OverJet(bool charZero, Formula body) => OverK("Field", charZero,
        All("j", Call("Jet", K), Implies(And(Call("N", J), Call("G", J)), body)));

    private static Formula OverK(string algebra, bool charZero, Formula body)
    {
        Formula typeclass = Seq(OpenBracket, Call(algebra, K), CloseBracket);
        return All("K", Op("Type"), charZero
            ? Seq(typeclass, Sp, OpenBracket, Call("CharZero", K), CloseBracket, Sp, body)
            : Seq(typeclass, Sp, body));
    }

    private static Formula Gamma(params Formula[] indices) =>
        new Formula.Apply(F.Gamma, [J, .. indices]);

    private static Formula Sum(string name, Formula body) =>
        Seq(F.Sum, Underscore, Grp(Seq(F.Id(name), Sp, InMacro, Sp, Index)), Sp, body);

    private static Formula All(string name, Formula ty, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), ty, body);

    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Op(name), [.. args]);
    private static Formula Parens(Formula x) => Seq(Open, x, Close);
    private static Formula MinusOf(Formula x) => Seq(Minus, Sp, x);
    private static Formula Half(Formula x) => Seq(Frac, Grp(x), Grp(Two));
    private static Formula Square(Formula x) => Seq(Parens(x), Caret, Grp(Two));
    private static Formula Plus(Formula x, Formula y) => Seq(x, Sp, F.Plus, Sp, y);
    private static Formula Subtract(Formula x, Formula y) => Seq(x, Sp, Minus, Sp, y);
    private static Formula Ne(Formula x, Formula y) => NotEqual(x, y);
    private static Formula Implies(Formula x, Formula y) => Parens(Seq(x, Sp, F.Implies, Sp, y));
    private static Formula Equivalent(Formula x, Formula y) => Parens(Seq(x, Sp, Iff, Sp, y));

    private static Formula Mul(params Formula[] terms) => Join(Cdot, terms);
    private static Formula And(params Formula[] terms) => Parens(Join(Land, terms));
    private static Formula Join(Formula op, Formula[] terms)
    {
        var parts = new List<Formula> { terms[0] };
        foreach (Formula term in terms[1..])
            parts.AddRange([Sp, op, Sp, term]);
        return Seq([.. parts]);
    }

    private static DocumentBlock Node(string id, string name, string title, Formula formula, string prose,
        LibraryNoteRef? citation = null) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            citation is null ? AssessedProvenance.FromRepo() : AssessedProvenance.FromRepo(citation),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
