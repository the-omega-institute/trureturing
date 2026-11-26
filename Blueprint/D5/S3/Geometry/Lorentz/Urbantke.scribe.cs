using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class UrbantkeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/Urbantke.";
    private static LibraryNoteRef Urbantke => LibraryNoteRef.Create("D5/L/LieTheory/urbantke1984plebanski");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal Urbantke metric identities, chiral reconstruction and Lorentzian conformal reality.",
        H("The Urbantke conformal metric from three two-forms"),
        Blocks(
            Paragraph(Text(
                "A triple of two-forms in dimension four determines a cubic metric density U. "
                + "The density is invertible exactly when the wedge Gram matrix Q is invertible. "
                + "In that case the triple spans a chiral plane and determines one conformal class.")),
            Node("urbantke-identities", "urbantke_polynomial_identities", "Universal polynomial identities",
                "Order the bivectors as (01, 02, 03, 23, 31, 12), so W exchanges the first and last blocks of three coordinates. "
                + "Write Q(B) = BᵀWB and D(B) = det Q(B)/8. The symbols ε(i,j,k) and ε(c,d,e,f) equal 1 on the increasing tuples. The entry U(a,b) contracts their product against B(a,c,i)B(b,d,j)B(e,f,k) with coefficient 1/12. The internal contraction is a determinant of three rows. "
                + "In the alternating spacetime contraction, interchanging the last two indices contributes a second equal term. This gives the coefficient 1/6 in the oriented-pair sum from the coefficient 1/12 in the full contraction. "
                + "When the electric block E is invertible, changing the internal basis by its inverse puts the triple on the graph [I; H]. The determinant of the basis change scales U once and D twice. "
                + "The symmetric part S of H gives Q = 2S. The skew part gives a determinant-one coframe shear L, and the cubic is Lᵀ diag(1, adj S) L. "
                + "The determinant of adj S is (det S)², and the spatial second exterior block of adj S is (det S)S. Together with adj S · S = (det S)I these prove the identities in the symmetric chart, including singular S. "
                + "Exterior wedge covariance transports the minor identity through L. After undoing the internal basis change, replace E by E + tI. "
                + "Its determinant is a monic cubic in t. Each claimed entry identity holds at infinitely many t, so its polynomial difference vanishes at t = 0.",
                PolynomialIdentities(), true),
            Node("urbantke-chiral-star", "urbantke_nondegenerate_iff_and_chiral_star", "Nondegeneracy and the chiral plane",
                "The determinant identity gives the nondegeneracy equivalence. Invertibility of Q makes multiplication by B injective, so the columns span a three-dimensional subspace. "
                + "The two-form Hodge operator is H = DW(Λ²U)⁻¹. The wedge determinant identity gives H² = I, and the minor identity says H fixes B. "
                + "Complementary oriented minors give trace H = 0. The projector (I + H)/2 has trace and rank three, so its range is the column span. "
                + "The opposite eigenspace is its W-orthogonal complement by W-self-adjointness and the invertibility of Q.",
                ChiralStar()),
            Node("exterior-square-scalar", "exteriorSquare_eq_smul_id_imp_scalar", "Scalar rigidity of the second exterior power",
                "Proportionality of the oriented minors gives proportionality in either orientation of a pair. "
                + "For distinct row indices k and i, choose j distinct from both. The principal minor in i,j is nonzero, and the two minors with rows k,j and k,i and columns i,j vanish. "
                + "Eliminating the off-diagonal entries gives Aₖᵢ = 0. Each product of two distinct diagonal entries then equals c, so every diagonal entry is nonzero and the diagonal entries agree.",
                ScalarRigidity()),
            Node("urbantke-conformal-uniqueness", "urbantke_conformal_uniqueness", "Conformal uniqueness from exterior squares",
                "Multiplicativity of exterior squares reduces the proportionality to a scalar exterior square for g₂g₁⁻¹. Scalar rigidity gives a nonzero factor relating the metrics.",
                ConformalUniqueness()),
            Node("urbantke-chiral-uniqueness", "urbantke_conformal_uniqueness_of_chiral_plane", "Conformal uniqueness from a chiral plane",
                "For volumes whose squares are the metric determinants, the stars square to the identity. Assigning the same wedge-nondegenerate plane eigenvalue +1 forces eigenvalue −1 on its W-orthogonal complement. "
                + "These two subspaces span the bivector space, so the two stars agree. The exterior squares then differ by the ratio of volume coefficients.",
                ChiralUniqueness()),
            Node("urbantke-lorentz-reality", "urbantke_lorentz_reality", "Lorentzian conformal reality",
                "The reality equation places the conjugate plane in the opposite chiral eigenspace. Nondegeneracy gives the complementary decomposition, and conjugation reverses the sign of the normalized star. "
                + "Conformal uniqueness makes the conjugate metric proportional to the original density. Dividing by a nonzero entry gives a real symmetric representative. "
                + "In this real scale the complex volume is nonzero and purely imaginary, so the real determinant is negative. The positive real volume coefficient is the square root of the determinant's absolute value, and its Hodge operator squares to −I. "
                + "A real nondegenerate symmetric form in four dimensions with negative determinant has one or three negative directions.",
                LorentzReality()),
            Node("urbantke-lorentz-witness", "urbantke_lorentz_witness", "The Lorentzian scalar graph",
                "For the graph with lower block iI, the symmetric spatial block has adjugate −I and the coframe shear is the identity. "
                + "The electric and magnetic blocks give the wedge Gram matrix 2iI, and replacing i by its conjugate in the second factor makes the mixed wedge Gram matrix zero.",
                LorentzWitness()),
            Node("simplicity-and-reality", "simplicity_not_sufficient_for_real_lorentz", "A simple complex triple without a real conformal metric",
                "For the graph with lower block (1+i)I, the wedge Gram matrix is a nonzero scalar multiple of I. Its Urbantke density has time entry 1 and spatial diagonal entries 2i. "
                + "A complex scale making the time entry real must itself be real and nonzero. It then leaves the nonzero imaginary spatial entries nonreal.",
                SimplicityWitness(), true)),
        []));

    private static DocumentBlock Node(string id, string name, string title, string prose,
        Formula formula, bool citeUrbantke = false) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)),
        citeUrbantke ? AssessedProvenance.FromRepo(Urbantke) : AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula PolynomialIdentities()
    {
        Formula k = F.Id("K");
        Formula b = F.Id("B");
        Formula u = Apply("U", b);
        Formula q = Apply("Q", b);
        return OverField(true, All("B", Triple(k), And(
            Equal(Transpose(u), u),
            Equal(Det(u), Divide(Squared(Det(q)), D(6, 4))),
            Equal(Multiply(Multiply(Exterior(u), Apply("W", k)), b),
                Scale(Divide(Det(q), D(8)), b)))));
    }

    private static Formula ChiralStar()
    {
        Formula k = F.Id("K");
        Formula b = F.Id("B");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula u = Apply("U", b);
        Formula q = Apply("Q", b);
        Formula h = Apply("H", u, Apply("D", b));
        Formula plus = All("x", Vector(D(6), k), Rel(Equal(Multiply(h, x), x), Iff,
            Ex("y", Vector(D(3), k), Equal(Multiply(b, y), x))));
        Formula minus = All("x", Vector(D(6), k), Rel(Equal(Multiply(h, x), Negative(x)), Iff,
            Equal(Multiply(Transpose(b), Multiply(Apply("W", k), x)), D(0))));
        return OverField(true, All("B", Triple(k), And(
            Rel(Nonzero(Det(u)), Iff, Nonzero(Det(q))),
            Rel(Nonzero(Det(q)), Implies, And(
                Apply("LinearIndependent", k, Apply("columns", b)),
                Equal(Apply("dim", Apply("Col", b)), D(3)),
                Equal(Squared(h), Identity(D(6))),
                Equal(Multiply(h, b), b), Parens(plus), Parens(minus))))));
    }

    private static Formula ScalarRigidity()
    {
        Formula k = F.Id("K");
        Formula a = F.Id("A");
        Formula c = F.Id("c");
        Formula r = F.Id("r");
        return OverField(false, All("A", Metric(k), All("c", k,
            Rel(And(Nonzero(c), Equal(Exterior(a), Scale(c, Identity(D(6))))), Implies,
                Ex("r", k, And(Nonzero(r), Equal(a, Scale(r, Identity(D(4))))))))));
    }

    private static Formula ConformalUniqueness()
    {
        Formula k = F.Id("K");
        Formula g = F.Id("g");
        Formula h = F.Id("h");
        Formula c = F.Id("c");
        return OverField(false, All("g", Metric(k), All("h", Metric(k), All("c", k,
            Rel(And(Nonzero(Det(g)), Nonzero(c), Equal(Exterior(h), Scale(c, Exterior(g)))), Implies,
                Conformal(k, g, h))))));
    }

    private static Formula ChiralUniqueness()
    {
        Formula k = F.Id("K");
        Formula g = F.Id("g");
        Formula h = F.Id("h");
        Formula v = F.Id("v");
        Formula w = F.Id("w");
        Formula b = F.Id("B");
        Formula assumptions = And(
            Equal(Transpose(g), g), Equal(Transpose(h), h), Nonzero(Det(g)), Nonzero(Det(h)),
            Equal(Squared(v), Det(g)), Equal(Squared(w), Det(h)), Nonzero(Det(Apply("Q", b))),
            Equal(Multiply(Apply("H", g, v), b), b), Equal(Multiply(Apply("H", h, w), b), b));
        return OverField(true, All("g", Metric(k), All("h", Metric(k), All("v", k, All("w", k,
            All("B", Triple(k), Rel(assumptions, Implies, Conformal(k, g, h))))))));
    }

    private static Formula LorentzReality()
    {
        Formula c = NumberField("C");
        Formula r = NumberField("R");
        Formula b = F.Id("B");
        Formula g = F.Id("g");
        Formula a = F.Id("a");
        Formula volume = Seq(Sqrt, Grp(Seq(Lvert, Sp, Det(g), Sp, Rvert)));
        return All("B", Triple(c), Rel(
            And(Nonzero(Det(Apply("Q", b))), Equal(Multiply(
                Multiply(Transpose(b), Apply("W", c)), Conjugate(b)), D(0))), Implies,
            Ex("g", Metric(r), Ex("a", c, And(Nonzero(a), Equal(Transpose(g), g),
                Rel(Det(g), Lt, D(0)), Equal(Apply("U", b), Scale(a, Complexify(g))),
                Equal(Squared(Apply("H", g, volume)), Negative(Identity(D(6)))))))));
    }

    private static Formula LorentzWitness()
    {
        Formula i = Operator("i");
        Formula c = NumberField("C");
        Formula b = Apply("graph", i);
        Formula u = Apply("diag", D(1), Negative(D(1)), Negative(D(1)), Negative(D(1)));
        return And(Equal(Apply("Q", b), Scale(Multiply(D(2), i), Identity(D(3)))),
            Equal(Apply("U", b), u),
            Equal(Multiply(Multiply(Transpose(b), Apply("W", c)), Conjugate(b)), D(0)),
            Equal(Apply("D", b), Negative(i)));
    }

    private static Formula SimplicityWitness()
    {
        Formula c = NumberField("C");
        Formula r = NumberField("R");
        Formula i = Operator("i");
        Formula z = Add(D(1), i);
        Formula b = Apply("graph", z);
        Formula q = Apply("Q", b);
        Formula u = Apply("U", b);
        Formula twoI = Multiply(D(2), i);
        Formula a = F.Id("a");
        Formula g = F.Id("g");
        return And(Equal(q, Scale(Multiply(D(2), z), Identity(D(3)))),
            Nonzero(Det(q)), Equal(u, Apply("diag", D(1), twoI, twoI, twoI)),
            Seq(Neg, Sp, Ex("g", Metric(r), Ex("a", c, Equal(u, Scale(a, Complexify(g)))))));
    }

    private static Formula Conformal(Formula k, Formula g, Formula h)
    {
        Formula a = F.Id("a");
        return Ex("a", k, And(Nonzero(a), Equal(h, Scale(a, g))));
    }

    private static Formula OverField(bool characteristicZero, Formula body)
    {
        Formula k = F.Id("K");
        Formula field = Seq(OpenBracket, Apply("Field", k), CloseBracket);
        Formula classes = characteristicZero
            ? Seq(field, Sp, OpenBracket, Apply("CharZero", k), CloseBracket)
            : field;
        return All("K", Operator("Type"), Seq(classes, Sp, body));
    }

    private static Formula NumberField(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula Metric(Formula k) => MatrixType(D(4), D(4), k);
    private static Formula Triple(Formula k) => MatrixType(D(6), D(3), k);
    private static Formula MatrixType(Formula m, Formula n, Formula k) =>
        new Formula.Apply(Seq(Operator("Mat"), Underscore, Grp(Seq(m, Sp, Times, Sp, n))), [k]);
    private static Formula Vector(Formula size, Formula k) => Seq(k, Caret, Grp(size));
    private static Formula Operator(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Apply(string name, params Formula[] args) => new Formula.Apply(Operator(name), [.. args]);
    private static Formula Identity(Formula n) => Seq(F.Id("I"), Underscore, Grp(n));
    private static Formula Det(Formula matrix) => Apply("det", matrix);
    private static Formula Transpose(Formula matrix) => Seq(Parens(matrix), Caret, Grp(F.Id("T")));
    private static Formula Exterior(Formula matrix) =>
        new Formula.Apply(Seq(Lambda, Caret, Grp(D(2))), [matrix]);
    private static Formula Complexify(Formula matrix) => Apply("complexify", matrix);
    private static Formula Conjugate(Formula matrix) => Seq(Overline, Grp(matrix));
    private static Formula Squared(Formula value) => Seq(Parens(value), Caret, Grp(D(2)));
    private static Formula Scale(Formula scalar, Formula matrix) => Rel(scalar, Cdot, matrix);
    private static Formula Divide(Formula numerator, Formula denominator) => Seq(Frac, Grp(numerator), Grp(denominator));
    private static Formula Negative(Formula value) => Seq(Minus, Sp, value);
    private static Formula Nonzero(Formula value) => NotEqual(value, D(0));
    private static Formula Parens(Formula formula) => Seq(Open, formula, Close);
    private static Formula Rel(Formula left, Formula relation, Formula right) =>
        Parens(Seq(left, Sp, relation, Sp, right));
    private static Formula And(params Formula[] terms)
    {
        var parts = new List<Formula> { terms[0] };
        foreach (Formula term in terms[1..])
            parts.AddRange([Sp, Land, Sp, term]);
        return Parens(Seq([.. parts]));
    }
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
}
