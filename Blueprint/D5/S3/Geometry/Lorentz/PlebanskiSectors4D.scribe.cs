using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class PlebanskiSectors4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/PlebanskiSectors4D.";
    private static LibraryNoteRef Urbantke => LibraryNoteRef.Create("D5/L/LieTheory/urbantke1984plebanski");
    private static LibraryNoteRef DePietriFreidel =>
        LibraryNoteRef.Create("D5/L/LieTheory/depietrifreidel1999plebanski");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The algebraic geometry of the four-dimensional chiral simplicity equations.",
        H("Plebański simplicity for triples of two-forms"),
        Blocks(
            Paragraph(Text("Use the oriented pair basis (01, 02, 03, 23, 31, 12). "
                + "The wedge Gram matrix Q is the matrix of wedge pairings relative to the coordinate volume. "
                + "Simplicity means Q is its mean trace times the identity. "
                + "The model G(z) has upper block I and lower block zI. "
                + "A coframe acts by its second exterior power, written act. "
                + "The five coordinates are Q₀₁, Q₀₂, Q₁₂, Q₀₀ − Q₂₂, and Q₁₁ − Q₂₂. "
                + "The function signValue takes true to 1 and false to −1. "
                + "The sector with labels t and s is signValue(t) times G(z signValue(s)). "
                + "The model metric is diag(1,z²,z²,z²). "
                + "The function sumsquares adds the squares of the four coordinates.")),
            Node("simplicity-equations", "simple_iff_five_eq_zero", "Five simplicity equations",
                "The three off-diagonal entries and two differences of diagonal entries vanish exactly when the symmetric Gram matrix is scalar.",
                Field(true, All("B", Triple(K), Rel(Apply("Simple", B), Iff,
                    Equal(Apply("five", Q(B)), D(0)))))),
            Node("simplicity-expansion", "simplicity_expansion", "Quadratic expansion",
                "The coefficient of the first power of the parameter defines the Jacobian.",
                Field(false, All("B", Triple(K), All("X", Triple(K), All("t", K, Equal(
                    Apply("five", Q(Add(B, Scale(T, X)))),
                    Add(Add(Apply("five", Q(B)), Scale(T, Deriv(B, X))),
                        Scale(Squared(T), Apply("five", Q(X)))))))))),
            Node("simplicity-jacobian-surjective", "simplicityDeriv_surjective", "Surjective Jacobian",
                "Full column rank gives a right inverse to the transposed triple. "
                + "The wedge pairing is an involution. Apply the right inverse and wedge pairing to half of a symmetric lift of the coordinates.",
                Field(true, All("B", Triple(K), Rel(FullColumns(B), Implies,
                    Apply("Surjective", Deriv(B)))))),
            Node("simplicity-jacobian-rank", "simplicity_jacobian_rank", "Jacobian rank and tangent dimension",
                "The five equations have independent derivatives at every triple with independent columns. "
                + "Rank-nullity in the eighteen-dimensional space of triples gives the dimension of the tangent space at any such solution.",
                Field(true, All("B", Triple(K), Rel(FullColumns(B), Implies,
                    And(Equal(Apply("dim", Apply("range", Deriv(B))), D(5)),
                        Equal(Apply("dim", Apply("ker", Deriv(B))), D(1, 3))))))),
            Node("wedge-gram-covariance", "wedgeGram_action", "Coframe covariance of the Gram matrix",
                "The wedge pairing scales by the coframe determinant, including when the coframe is singular.",
                Field(false, All("A", Metric(K), All("B", Triple(K), Equal(Q(Act(A, B)),
                    Scale(Det(A), Q(B))))))),
            Node("urbantke-covariance", "urbantke_action", "Coframe covariance of the cubic",
                "Write each term of the cubic as a product of two skew matrices and the skew matrix of a complementary bivector. "
                + "The wedge law contracts the two middle coframe factors. The two free factors act by congruence.",
                Field(false, All("A", Metric(K), All("B", Triple(K), Equal(U(Act(A, B)),
                    Scale(Det(A), Multiply(Multiply(A, U(B)), Transpose(A))))))), Urbantke),
            Node("simplicity-sign", "simplicity_neg", "Negation of the triple",
                "Negation preserves the quadratic Gram matrix and reverses the cubic Urbantke density.",
                Field(false, All("B", Triple(K), And(Equal(Q(Negative(B)), Q(B)),
                    Equal(U(Negative(B)), Negative(U(B))))))),
            Node("degenerate-simplicity", "degenerate_simplicity_witnesses", "Two degenerate simplicity witnesses",
                "The upper identity block gives the triple of wedges with a common covector. Its Urbantke matrix has a single nonzero entry. "
                + "The lower identity block gives the three spatial wedges. In its cubic every term contains a row involving the time index.",
                Field(true, And(Equal(Q(Model(D(0))), D(0)),
                    Equal(Apply("rank", U(Model(D(0)))), D(1)),
                    Nonzero(Operator("spatial")), Equal(Q(Operator("spatial")), D(0)),
                    Equal(U(Operator("spatial")), D(0)))), Urbantke),
            Node("graph-normal-form", "exists_graph_model", "Characteristic-zero normal form",
                "Nondegeneracy makes the symmetric Urbantke density invertible. A determinant-one shear brings a nonzero value of its quadratic form to the time entry, which is the electric determinant. "
                + "Normalize the electric block by a spatial coframe. Simplicity then makes the symmetric part of the magnetic block scalar. A second shear supplies its skew part.",
                Field(true, All("B", Triple(K), Rel(NondegenerateSimple(B), Iff,
                    Ex("A", Metric(K), Ex("z", K, And(Nonzero(Det(A)), Nonzero(Z),
                        Equal(B, Act(A, Model(Z))))))))), Urbantke),
            Node("graph-orbit", "model_orbit_iff", "Four-square orbit criterion",
                "Comparing Gram matrices fixes the relative coframe determinant. Comparing the time entry of the cubic expresses that determinant as a sum of four squares. "
                + "For the converse, quaternion right multiplication scales the unit model by the quaternion norm. Spatial dilations transport this identity to the two models.",
                Field(true, All("z", K, All("w", K, Rel(And(Nonzero(Z), Nonzero(F.Id("w"))), Implies,
                    Rel(Ex("A", Metric(K), And(Nonzero(Det(A)),
                            Equal(Act(A, Model(Z)), Model(F.Id("w"))))),
                        Iff, Ex("q", Vector(D(4), K), Equal(Apply("sumsquares", F.Id("q")),
                            Divide(F.Id("w"), Z))))))))),
            Node("euclidean-model", "euclidean_model_iff", "Oriented Euclidean normal form",
                "A positive ratio of scalar graph parameters is a real square. Time reflection reverses coframe orientation and switches the two signs in the model. "
                + "The overall sign and chirality give four labels for the oriented models.",
                All("B", Triple(RealField), Rel(NondegenerateSimple(B), Iff,
                    Ex("A", Metric(RealField), Ex("t", BoolType, Ex("s", BoolType, And(
                        Rel(D(0), Lt, Det(A)), Equal(B, Act(A, Sector(D(1), T, F.Id("s")))))))))),
                DePietriFreidel),
            Node("fixed-metric-sector-orbit", "fixed_metric_sector_orbit_iff", "Orbits at a fixed metric",
                "For a fixed normalized metric, its two oriented coframes have the same positive determinant. "
                + "The Gram scalar and cubic density distinguish the chiral and overall labels. "
                + "The quotient of the two coframes is an oriented real isometry and maps representatives with matching labels.",
                FixedMetric(), DePietriFreidel),
            Node("lorentzian-model", "lorentzian_model_iff", "Oriented Lorentzian normal form",
                "The phase conditions require the mixed wedge Gram matrix to vanish, the cubic density to equal its entrywise conjugate, and the mean trace of the Gram matrix to be purely imaginary. "
                + "The real symmetric cubic density has negative determinant. Its spectral factorization gives an oriented real coframe with the required Gram scalar and cubic density. "
                + "These two quantities determine a common Hodge eigenspace and leave a complex orthogonal frame change of determinant one. A quaternion construction lifts that change to a real coframe action of determinant one. "
                + "Conversely, the model and every positively oriented real coframe image satisfy the phase conditions.",
                LorentzianModel(), Urbantke),
            Node("oriented-sector-hodge", "oriented_sector_hodge", "Hodge eigenvalues of the oriented sectors",
                "Use the coframe determinant as the volume coefficient. The overall sign affects the cubic density and cancels in the exterior square used by the Hodge operator. "
                + "The second label gives the Hodge eigenvalue. It is plus or minus one for the Euclidean model and plus or minus the imaginary unit for the Lorentzian model, with true denoting self-duality in both cases.",
                OrientedHodge(), Urbantke)),
        []));

    private static Formula LorentzianModel()
    {
        Formula sd = F.Id("s");
        Formula imaginaryUnit = Seq(Mathrm, Grp(F.Id("i")));
        Formula reality = And(
            Equal(Multiply(Multiply(Transpose(B), Apply("W", ComplexField)), Apply("conj", B)), D(0)),
            Equal(Apply("conj", U(B)), U(B)),
            Equal(Apply("Re", Apply("gramScalar", B)), D(0)));
        Formula representative = Ex("A", Metric(RealField), Ex("t", BoolType, Ex("s", BoolType,
            And(Rel(D(0), Lt, Det(A)),
                Equal(B, Act(Apply("realCast", A), Sector(imaginaryUnit, T, sd)))))));
        return All("B", Triple(ComplexField), Rel(And(NondegenerateSimple(B), reality), Iff, representative));
    }

    private static Formula OrientedHodge()
    {
        Formula sd = F.Id("s");
        Formula sector = Act(A, Sector(Z, T, sd));
        Formula metric = Multiply(Multiply(A, Apply("modelMetric", Z)), Transpose(A));
        Formula hypotheses = And(Equal(Seq(Z, Caret, Grp(D(4))), D(1)), Nonzero(Det(A)));
        Formula eigenvalue = Multiply(Z, Apply("signValue", sd));
        Formula identity = Equal(Multiply(Apply("hodge", metric, Det(A)), sector), Scale(eigenvalue, sector));
        return Field(true, All("z", K, All("A", Metric(K), All("t", BoolType, All("s", BoolType,
            Rel(hypotheses, Implies, identity))))));
    }

    private static Formula FixedMetric()
    {
        Formula f = F.Id("f");
        Formula j = F.Id("j");
        Formula g = F.Id("g");
        Formula c = F.Id("C");
        Formula l = F.Id("L");
        Formula s = F.Id("s");
        Formula v = F.Id("v");
        Formula w = F.Id("w");
        Formula map(Formula a) => new Formula.Apply(f, [a]);
        Formula congruence(Formula a) => Multiply(Multiply(a, j), Transpose(a));
        Formula hypotheses = And(Nonzero(Z), Equal(map(j), Apply("modelMetric", Z)),
            Nonzero(Det(g)), Rel(D(0), Lt, Det(A)), Rel(D(0), Lt, Det(c)),
            Equal(congruence(A), g), Equal(congruence(c), g));
        Formula orbit = Ex("L", Metric(RealField), And(Apply("OrientedIsometry", g, l),
            Equal(Act(map(l), Act(map(A), Sector(Z, T, s))), Act(map(c), Sector(Z, v, w)))));
        Formula labels = And(Equal(T, v), Equal(s, w));
        Formula body = Rel(hypotheses, Implies, Rel(orbit, Iff, labels));
        foreach (string name in new[] { "w", "v", "s", "t" })
            body = All(name, BoolType, body);
        foreach (string name in new[] { "C", "A", "g", "j" })
            body = All(name, Metric(RealField), body);
        return Field(true, All("f", Apply("RingHom", RealField, K), All("z", K, body)));
    }

    private static DocumentBlock Node(string id, string name, string title, string prose,
        Formula formula, LibraryNoteRef? note = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)),
        note is null ? AssessedProvenance.FromRepo() : AssessedProvenance.FromRepo(note),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula K => F.Id("K");
    private static Formula A => F.Id("A");
    private static Formula B => F.Id("B");
    private static Formula X => F.Id("X");
    private static Formula Z => F.Id("z");
    private static Formula T => F.Id("t");
    private static Formula RealField => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula ComplexField => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula BoolType => Operator("Bool");
    private static Formula Q(Formula b) => Apply("Q", b);
    private static Formula U(Formula b) => Apply("U", b);
    private static Formula Act(Formula a, Formula b) => Apply("act", a, b);
    private static Formula Model(Formula z) => Apply("G", z);
    private static Formula Sector(Formula z, Formula t, Formula s) => Apply("sectorModel", z, t, s);
    private static Formula Deriv(params Formula[] args) => Apply("Jacobian", args);
    private static Formula NondegenerateSimple(Formula b) => And(Apply("Simple", b), Nonzero(Det(Q(b))));
    private static Formula FullColumns(Formula b) => Apply("LinearIndependent", K, Apply("columns", b));
    private static Formula Field(bool characteristicZero, Formula body)
    {
        Formula field = Seq(OpenBracket, Apply("Field", K), CloseBracket);
        return All("K", Operator("Type"), Seq(field, Sp, characteristicZero
            ? Seq(OpenBracket, Apply("CharZero", K), CloseBracket, Sp, body)
            : body));
    }

    private static Formula Metric(Formula k) => MatrixType(D(4), D(4), k);
    private static Formula Triple(Formula k) => MatrixType(D(6), D(3), k);
    private static Formula MatrixType(Formula m, Formula n, Formula k) =>
        new Formula.Apply(Seq(Operator("Mat"), Underscore, Grp(Seq(m, Sp, Times, Sp, n))), [k]);
    private static Formula Vector(Formula size, Formula k) => Seq(k, Caret, Grp(size));
    private static Formula Operator(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Apply(string name, params Formula[] args) => new Formula.Apply(Operator(name), [.. args]);
    private static Formula Det(Formula matrix) => Apply("det", matrix);
    private static Formula Transpose(Formula matrix) => Seq(Parens(matrix), Caret, Grp(F.Id("T")));
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
