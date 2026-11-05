using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Contextuality;

internal sealed class LinearDoilyNegativeLineParityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/QuantumContext/mullersanigagiorgettideboutrayholweck2022doilies");

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Binary => Call("ZMod", D(2));
    private static Formula Label => Parenthesized(Seq(Binary, Sp, Times, Sp, Binary));
    private static Formula N => F.Id("N");
    private static Formula U => F.Id("U");
    private static Formula V => F.Id("v");
    private static Formula W => F.Id("w");
    private static Formula LowerU => F.Id("u");
    private static Formula LowerL => F.Id("l");
    private static Formula Vector => Arrow(Call("Fin", N), Label);
    private static Formula Subspace => Call("Submodule", Binary, Vector);
    private static Formula PointSet => Call("Finset", Vector);
    private static Formula MatrixType => Call("Matrix",
        Arrow(Call("Fin", N), Call("Fin", D(2))),
        Arrow(Call("Fin", N), Call("Fin", D(2))), Complexes);
    private static Formula ZeroVector => Typed(D(0), Vector);
    private static Formula ZeroBinary => Typed(D(0), Binary);
    private static Formula MatrixOne => Typed(D(1), MatrixType);
    private static Formula NegativeIdentity => new Formula.Negate(Parenthesized(MatrixOne));
    private static Formula AllN(Formula body) => All(N, Naturals, body);
    private static Formula AllU(Formula body) => AllN(All(U, Subspace, body));

    private static Formula CanonicalLabelDefinition
    {
        get
        {
            var p = F.Id("p");
            return All(p, Label, Eq(Call("canonicalLabel", p),
                If(Eq(Projection(p, D(1)), ZeroBinary),
                    If(Eq(Projection(p, D(2)), ZeroBinary),
                        Qualified("Pauli", "I"), Qualified("Pauli", "Z")),
                    If(Eq(Projection(p, D(2)), ZeroBinary),
                        Qualified("Pauli", "X"), Qualified("Pauli", "Y")))));
        }
    }

    private static Formula ObservableDefinition => AllN(All(V, Vector,
        Eq(Call("observable", V), Call("wordOp",
            Lambda(F.Id("j"), Call("Fin", N),
                Call("canonicalLabel", App(V, F.Id("j"))))))));

    private static Formula FormDefinition
    {
        get
        {
            var j = F.Id("j");
            return AllN(All(V, Vector, All(W, Vector,
                Eq(Call("B", V, W), SumOver(j, Call("Fin", N),
                    Add(Mul(Projection(App(V, j), D(1)), Projection(App(W, j), D(2))),
                        Mul(Projection(App(V, j), D(2)), Projection(App(W, j), D(1)))))))));
        }
    }

    private static Formula DoilyDefinition => AllU(Eq(Call("IsLinearDoily", U),
        Parenthesized(And(
            Eq(Call(Qualified("Module", "finrank"), Binary,
                Call(Qualified("CoeSort", "coe"), U)), Typed(D(4), Naturals)),
            All(LowerU, Vector, Imp(Member(LowerU, U),
                Imp(All(W, Vector, Imp(Member(W, U), Eq(Call("B", LowerU, W), ZeroBinary))),
                    Eq(LowerU, ZeroVector))))))));

    private static Formula PointsDefinition => AllU(Eq(Call("points", U),
        Filter(Typed(Qualified("Finset", "univ"), PointSet), V, Vector,
            And(Member(V, U), Ne(V, ZeroVector)))));

    private static Formula LinesDefinition => AllU(Eq(Call("lines", U),
        Filter(Call(Qualified("Finset", "powerset"), Call("points", U)), LowerL, PointSet,
            And(Eq(Call(Qualified("Finset", "card"), LowerL), Typed(D(3), Naturals)),
                All(LowerU, Vector, Imp(Member(LowerU, LowerL),
                    All(V, Vector, Imp(Member(V, LowerL), Imp(Ne(LowerU, V),
                        And(Member(Add(LowerU, V), LowerL),
                            Eq(Call("B", LowerU, V), ZeroBinary)))))))))));

    private static Formula LineProductDefinition => AllN(All(LowerL, PointSet,
        Eq(Call("lineProduct", LowerL), Call(Qualified("List", "prod"),
            Call(Qualified("List", "map"), Named("observable"),
                Call(Qualified("Finset", "toList"), LowerL))))));

    private static Formula NegativeLinesDefinition => AllU(Eq(Call("negativeLines", U),
        Filter(Call("lines", U), LowerL, PointSet,
            Eq(Call("lineProduct", LowerL), NegativeIdentity))));

    private static Formula ClaimBody => AllN(Imp(LE(Typed(D(2), Naturals), N),
        All(U, Subspace, Imp(Call("IsLinearDoily", U),
            Call("Odd", Call(Qualified("Finset", "card"), Call("negativeLines", U)))))));

    private static Formula Quaternary => Call("ZMod", D(4));
    private static Formula NatToQuaternary(Formula value) =>
        Typed(Call(Qualified("Nat", "cast"), Typed(value, Naturals)), Quaternary);
    private static Formula LabelVal(Formula value, byte coordinate) =>
        Call(Qualified("ZMod", "val"), Projection(value, D(coordinate)));
    private static Formula LabelProduct(Formula value) =>
        Mul(LabelVal(value, 1), LabelVal(value, 2));
    private static Formula LocalExponentDefinition => All(LowerU, Label, All(V, Label,
        Eq(Typed(Call("localExponent", LowerU, V), Quaternary),
            Add(new Formula.Binary(
                    Parenthesized(Add(NatToQuaternary(LabelProduct(LowerU)),
                        NatToQuaternary(LabelProduct(V)))),
                    FormulaBinaryOperator.Subtract,
                    Parenthesized(NatToQuaternary(LabelProduct(Add(LowerU, V))))),
                Mul(Typed(D(2), Quaternary),
                    NatToQuaternary(Mul(LabelVal(LowerU, 2), LabelVal(V, 1))))))));

    private static Formula ImaginaryFourthPower => Seq(Operatorname, Grp(Seq(
        F.Id("Complex"), Dot,
        new Formula.Subscript(F.Id("I"), Seq(F.Id("pow"), Esc, F.Id("four"))))));
    private static Formula PhaseDefinition => AllN(All(LowerU, Vector, All(V, Vector,
        Eq(Typed(Call("phase", LowerU, V), Complexes),
            Seq(new Formula.Subscript(Prod, Typed(F.Id("j"), Call("Fin", N))), Sp,
                Parenthesized(App(Call(Qualified("DFunLike", "coe"),
                        Call(Qualified("AddChar", "zmodChar"), Typed(D(4), Naturals), ImaginaryFourthPower)),
                    Call("localExponent", App(LowerU, F.Id("j")), App(V, F.Id("j"))))))))));

    private static Formula FormSymmetry => AllN(All(LowerU, Vector, All(V, Vector,
        Eq(Call("B", LowerU, V), Call("B", V, LowerU)))));
    private static Formula FormAddRight => AllN(All(LowerU, Vector, All(V, Vector, All(W, Vector,
        Eq(Call("B", LowerU, Add(V, W)), Add(Call("B", LowerU, V), Call("B", LowerU, W)))))));
    private static Formula FormSelf => AllN(All(LowerU, Vector,
        Eq(Call("B", LowerU, LowerU), ZeroBinary)));
    private static Formula TripleProduct => AllN(All(LowerU, Vector, All(V, Vector,
        Imp(Ne(LowerU, ZeroVector), Imp(Ne(V, ZeroVector), Imp(Ne(LowerU, V),
            Imp(Eq(Call("B", LowerU, V), ZeroBinary),
                Eq(Call("lineProduct", Call(Qualified("Finset", "insert"), LowerU,
                        Call(Qualified("Finset", "insert"), V,
                            Call(Qualified("Singleton", "singleton"), Add(LowerU, V))))),
                    Seq(Parenthesized(Typed(Call("phase", LowerU, V), Complexes)), Sp, Cdot, Sp,
                        Parenthesized(MatrixOne))))))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every linear N-qubit doily has an odd number of negative lines.",
        H("Odd negative-line parity in linear doilies"),
        Blocks(
            Definition("canonical-label", "Canonical single-qubit labels", "canonicalLabel",
                CanonicalLabelDefinition, AssessedProvenance.FromLiterature(Source),
                "The four binary pairs label I, Z, X and Y, with Y = iXZ. "
                + "The first coordinate is the exponent of X and the second that of Z. "
                + "These coordinates exchange the two entries of the paper's convention "
                + "in xiv-MSGDH2.tex, lines 288–295; the observables are the same unsigned Pauli matrices."),
            Definition("observable", "Tensor products of canonical Pauli matrices", "observable",
                ObservableDefinition, AssessedProvenance.FromLiterature(Source),
                "For a binary label v on N qubits, take the tensor product of the matrices "
                + "specified by canonicalLabel at each coordinate j. The rows and columns are "
                + "indexed by functions from Fin N to Fin 2. This includes the identity when v is zero. "
                + "The unsigned tensor products are defined in xiv-MSGDH2.tex, lines 273–283."),
            Definition("symplectic-form", "The binary commutation form", "B",
                FormDefinition, AssessedProvenance.FromLiterature(Source),
                "The form sums the cross-coordinate products over all qubits in ZMod 2. "
                + "Two canonical observables commute precisely when this form vanishes. "
                + "It is the standard symplectic form in xiv-MSGDH2.tex, lines 222–231; "
                + "in characteristic two subtraction equals addition."),
            Definition("linear-doily", "Nondegenerate four-dimensional binary subspaces", "IsLinearDoily",
                DoilyDefinition, AssessedProvenance.FromLiterature(Source),
                "A linear doily is a four-dimensional binary subspace whose restricted symplectic "
                + "form has zero radical. CoeSort.coe U explicitly denotes the type coercion of U, "
                + "the underlying type of vectors in U in the dimension formula. The source defines a linear doily "
                + "as one spanning PG(3,2), in xiv-MSGDH2.tex, lines 1086–1087. "
                + "Over the binary field its fifteen points exhaust the nonzero vectors of that "
                + "four-space. A nonzero radical vector would be collinear with all fourteen "
                + "other points, whereas a point of the doily has six collinear neighbours. "
                + "Thus the restricted form is nondegenerate. Conversely a nondegenerate "
                + "binary four-space has the symplectic polar space W(3,2), the doily."),
            Definition("points", "The nonzero vectors of a subspace", "points",
                PointsDefinition, AssessedProvenance.FromLiterature(Source),
                "The points are exactly the vectors belonging to U other than zero. "
                + "There is one nonzero vector per projective point over the binary field. "
                + "This is the projective point description in xiv-MSGDH2.tex, lines 222–225."),
            Definition("lines", "Isotropic triples of points", "lines",
                LinesDefinition, AssessedProvenance.FromLiterature(Source),
                "Among all subsets of points U, retain the three-element sets such that "
                + "every pair of distinct vectors has zero symplectic pairing and has its sum "
                + "in the same set. Each is a triple consisting of u, v and u + v, hence the "
                + "nonzero vectors of a totally isotropic two-dimensional subspace. "
                + "The isotropic geometry and its observable interpretation are described "
                + "in xiv-MSGDH2.tex, lines 225–231 and 306–312."),
            Definition("line-product", "The matrix product of a finite set of observables", "lineProduct",
                LineProductDefinition, AssessedProvenance.FromRepo(Source),
                "Convert l to a list, replace each vector by its canonical observable, and "
                + "multiply the matrices in that order. The definition applies to every finite "
                + "set l. For an isotropic triple the three matrices commute, so the product "
                + "is independent of the chosen list order."),
            Definition("negative-lines", "Lines whose matrix product is minus identity", "negativeLines",
                NegativeLinesDefinition, AssessedProvenance.FromLiterature(Source),
                "A negative line is a line of U whose product is minus the identity matrix "
                + "on the N-qubit tensor space. The one in the formula is explicitly a matrix "
                + "identity, not a complex scalar. This is the sign convention in "
                + "xiv-MSGDH2.tex, lines 312–314."),
            Definition("claim", "The parity assertion for every number of qubits", "claim",
                Eq(Named("claim"), Parenthesized(ClaimBody)), AssessedProvenance.FromLiterature(Source),
                "For every natural N at least two and every nondegenerate four-dimensional "
                + "binary subspace U, the natural cardinality of negativeLines U is odd. "
                + "The source states this conjecture in xiv-MSGDH2.tex, lines 2255–2260. "
                + "Cardinalities and the dimension in these formulas are natural numbers; "
                + "neither is cast to an integer or a complex number."),
            Definition("local-exponent", "The single-qubit multiplication exponent", "localExponent",
                LocalExponentDefinition, AssessedProvenance.FromRepo(Source),
                "For binary labels u and v, take the natural representatives of their coordinates. "
                + "Cast each natural coordinate product into ZMod 4 before adding and subtracting. "
                + "The exponent is the product of the coordinates of u plus that of v, minus that "
                + "of their binary sum, plus twice the second coordinate of u times the first of v. "
                + "Thus subtraction takes place modulo four, rather than in the natural numbers."),
            Definition("phase", "The multiplication phase for Pauli words", "phase",
                PhaseDefinition, AssessedProvenance.FromRepo(Source),
                "Multiply the fourth roots of unity supplied by the single-qubit exponents over "
                + "all j in Fin N. The additive character sends a residue a modulo four to i "
                + "raised to its natural representative. DFunLike.coe denotes evaluation of "
                + "this character as a function; Complex.I_pow_four supplies the identity i to "
                + "the fourth power equals one. At N equal to zero the empty product is one."),
            PublishedTheorem("form-symmetry", "Symmetry of the binary form", "B_comm", FormSymmetry,
                "The form is symmetric: swapping u and v interchanges the two cross terms "
                + "in every coordinate, and commutativity of binary multiplication and addition "
                + "preserves their sum."),
            PublishedTheorem("form-add-right", "Additivity in the second argument", "B_add_right", FormAddRight,
                "The pairing of u with v + w is the sum of its pairings with v and w. "
                + "Symmetry reduces this to additivity in the first argument, where coordinate "
                + "distributivity and the finite-sum addition identity give the equality."),
            PublishedTheorem("form-self", "The form is alternating", "B_self", FormSelf,
                "In every coordinate the self-pairing is the sum of two equal binary products. "
                + "Their sum is zero in characteristic two, so the full self-pairing vanishes."),
            PublishedTheorem("line-product-triple", "The product of an isotropic triple", "lineProduct_triple",
                TripleProduct,
                "For distinct nonzero orthogonal labels u and v, the vectors u, v and u + v "
                + "are distinct. Their pairings vanish by symmetry, additivity and alternation, "
                + "so their observables commute. Reorder the finite-set product as the ordered "
                + "product of these three observables. Multiplication of the first two gives "
                + "phase u v times the observable of u + v. The latter squares to the identity, "
                + "giving the stated complex scalar times the matrix identity."),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Module + ".result"),
                H("Every linear doily has odd negative-line parity"),
                StatementSource.FromAuthor(Disp(ClaimBody)),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For two single-qubit labels, lift each binary coordinate to its natural "
                        + "representative zero or one. Form a residue modulo four by adding the "
                        + "coordinate products of the two labels, subtracting the coordinate "
                        + "product of their binary sum, and adding twice the second coordinate "
                        + "of the first label times the first coordinate of the second. The natural "
                        + "coordinate products are cast into ZMod 4 before adding or subtracting "
                        + "them, and the last product is multiplied there by two. "
                        + "The frozen Pauli letter multiplication and commutation identities, "
                        + "with binary labels and scalars normalized over the sixteen ordered "
                        + "label pairs, give the product as i to this exponent times the matrix "
                        + "of the sum. The commutation sign is plus one for zero binary "
                        + "symplectic pairing and minus one otherwise. "
                        + "Tensoring these identities gives the multiplication scalar and "
                        + "commutation sign for N qubits. The canonical Pauli word unit is its "
                        + "own inverse, so each observable squares to the identity. The square "
                        + "of the multiplication scalar is the sign of the symplectic pairing. "
                        + "For an isotropic pair this scalar is therefore plus or minus one. "
                        + "Every line is a triple of distinct nonzero vectors u, v and u + v, "
                        + "so its matrix product is plus or minus the identity.")),
                    Paragraph(Text(
                        "The binary form is bilinear, symmetric and alternating. Its restriction "
                        + "to U is nondegenerate by the defining radical condition. A symplectic "
                        + "basis therefore exists; dimension four forces exactly two symplectic "
                        + "pairs. Reorder that basis to obtain a linear equivalence e from "
                        + "Fin 4 → ZMod 2 to U, with coordinate pairings between positions zero "
                        + "and one and between positions two and three equal to one, and all "
                        + "other basis pairings zero. Thus the transported form on coordinates "
                        + "a and b is a 0 times b 1 plus a 1 times b 0 plus a 2 times b 3 "
                        + "plus a 3 times b 2.")),
                    Paragraph(Text(
                        "In this binary coordinate four-space, enumerate the fifteen distinct "
                        + "isotropic triples using the following ordered pairs, with each bit "
                        + "string giving coordinates zero through three: (0001,0100), (0001,1000), "
                        + "(0001,1100), (0010,0100), (0010,1000), (0010,1100), (0011,0100), "
                        + "(0011,1000), (0011,1100), (0101,1010), (0101,1011), (0110,1001), "
                        + "(0110,1011), (0111,1001), (0111,1010). "
                        + "Each representative is nonzero, the pair is distinct and orthogonal, "
                        + "and its sum is the third point. The fifteen triples are distinct "
                        + "and contain every triple generated by distinct nonzero orthogonal "
                        + "vectors. For any four single-qubit labels, evaluate these fifteen "
                        + "representative pairs by taking their binary linear combinations. "
                        + "The sum of their multiplication exponents in ZMod 4 equals twice "
                        + "the natural representative of the local symplectic pairing of the "
                        + "first two labels, cast into ZMod 4. This identity follows by checking "
                        + "all 256 assignments of the four labels.")),
                    Paragraph(Text(
                        "The additive character on ZMod 4 sending k to i raised to its natural "
                        + "representative converts addition into multiplication of fourth roots "
                        + "of unity. Its finite-product law and the local exponent identity "
                        + "make the product of the fifteen local scalars equal to the sign "
                        + "of the first local basis pairing. Linearity of e expresses each "
                        + "embedded vector at a qubit as the corresponding linear combination "
                        + "of the four basis labels at that qubit. Exchange the finite products "
                        + "over the fifteen pairs and over the N qubits. Multiplying the local "
                        + "signs adds their binary pairings, giving the sign of the global "
                        + "pairing of the first symplectic basis pair. That pairing is one, "
                        + "so the product of all fifteen multiplication scalars is minus one.")),
                    Paragraph(Text(
                        "Orthogonal vectors have commuting observables. Permuting the list "
                        + "of an isotropic triple therefore preserves its matrix product; "
                        + "multiplication of the first two observables followed by the square "
                        + "identity for their sum shows that this product is its multiplication "
                        + "scalar times the identity. Transport the fifteen coordinate triples "
                        + "through e. Every resulting triple is a line of U, every line of U "
                        + "arises in this way, and injectivity of e keeps distinct triples "
                        + "distinct. Thus this transport is a bijection onto lines U.")),
                    Paragraph(Text(
                        "For a finite family of complex signs, its product is minus one "
                        + "exactly when the number of entries equal to minus one is odd: "
                        + "the product is minus one raised to that natural cardinality. "
                        + "Multiplication of the identity matrix by a complex scalar is "
                        + "injective, since the identity matrix is nonzero. Apply this to the "
                        + "fifteen scalars. The matrix sign of each transported line shows "
                        + "that its scalar is plus or minus one, and the line is negative "
                        + "exactly when its scalar is minus one. Their total product is minus "
                        + "one, so an odd number of the scalars are negative. The line bijection "
                        + "identifies this count with the cardinality of negativeLines U. "
                        + "Choosing the symplectic equivalence for each U proves the assertion "
                        + "for every N at least two."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("muller-saniga-giorgetti-de-boutray-holweck-2022-linear-doily-odd-negative-lines"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock PublishedTheorem(string id, string title, string declaration,
        Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static DocumentBlock Definition(string id, string title, string declaration,
        Formula formula, AssessedProvenance provenance, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(Seq(F.Id(owner), Dot, F.Id(name))));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        Call(Named(name), arguments);
    private static Formula Call(Formula function, params Formula[] arguments) => App(function, arguments);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        Parenthesized(new Formula.TypeArrow(domain, codomain));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Lambda(Formula variable, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(variable, type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula Projection(Formula value, Formula index) =>
        Seq(Parenthesized(value), Dot, index);
    private static Formula If(Formula condition, Formula yes, Formula no) => Call("ite", condition, yes, no);
    private static Formula Filter(Formula set, Formula variable, Formula type, Formula condition) =>
        Call(Qualified("Finset", "filter"), Lambda(variable, type, condition), set);
    private static Formula SumOver(Formula variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(variable, type)), Sp, Parenthesized(body));
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
}
