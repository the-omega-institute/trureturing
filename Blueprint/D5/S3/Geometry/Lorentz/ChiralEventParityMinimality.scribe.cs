using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class ChiralEventParityMinimalityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Geometry/Lorentz/ChiralEventParityMinimality";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Geometry/lesterhaddadingripaios2022parity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Any two continuous invariant parity-odd real variables vanish together on a chiral four-particle event in each of the two event classes.",
        H("A lower bound of three chiral-event variables"),
        Blocks(
            Node("event", "event", "Ordered four-particle events", EventFormula(),
                "An event is an ordered quadruple of four-vectors, indexed in the order p, q, a, b. "
                    + "Each four-vector has type Fin 4 → ℝ, with coordinate zero the energy and coordinates one, two and three the spatial momentum, as in prelims.tex:21–23 of arXiv:2008.05206v6. "
                    + "The two interchangeable pairs are the first two and last two entries. "
                    + "The source's two event classes and their common symmetry group are specified in prelims.tex:656–666. "
                    + "The ambient type itself imposes no forward-cone or collision condition.", true),
            Node("eta", "eta", "The Minkowski metric matrix", EtaFormula(),
                "The diagonal matrix has signature (+,−,−,−), the convention of the source's Minkowski product. "
                    + "It also represents spatial parity on a four-vector.", true),
            Node("rotation", "rotation", "A proper spatial rotation", RotationFormula(),
                "The matrix fixes time and sends the spatial coordinates (x,y,z) to (−y,−x,−z). "
                    + "It preserves the Minkowski metric, has determinant one and has time-time entry one. "
                    + "Composing it with parity exchanges the first two spatial coordinates.", false),
            Node("minkowski", "minkowski", "The Minkowski product", MinkowskiFormula(),
                "The bilinear product multiplies the time coordinates and subtracts the three spatial coordinate products. "
                    + "The collision condition in prelims.tex:433–443 uses this product and its associated squared masses.", true),
            Node("forward-cone", "forwardCone", "Forward nonspacelike four-vectors", ForwardConeFormula(),
                "The time coordinate is nonnegative and its square bounds the squared spatial norm. "
                    + "Thus the zero vector and future null vectors are included, as in the set of four-vectors defined in prelims.tex:25–27.", true),
            Node("proper-orthochronous", "properOrthochronous", "Proper orthochronous Lorentz matrices", ProperFormula(),
                "The matrix preserves eta, has determinant one and has positive time-time entry. "
                    + "These conditions express the proper orthochronous Lorentz transformations used in the symmetry group of prelims.tex:190–193.", true),
            Node("parity-vector", "parityVector", "Parity of a four-vector", ParityVectorFormula(),
                "Parity fixes energy and negates all three spatial coordinates, as in prelims.tex:228–238.", true),
            Node("parity", "parity", "Parity of an event", ParityFormula(),
                "Apply four-vector parity to each of the four event entries. This is the componentwise event parity of prelims.tex:228–238.", true),
            Node("act", "act", "Lorentz transformations and pair permutations", ActFormula(),
                "The permutation sigma selects entries within the p,q pair and tau selects entries within the a,b pair; the same matrix lam then acts on every selected four-vector. "
                    + "Fin.castAdd embeds the first pair's indices into Fin 4, while Fin.natAdd shifts the second pair's indices by two. "
                    + "The formula defines the action for every real matrix; membership in the Lorentz group is required where the symmetry is used. "
                    + "This is the action described in prelims.tex:190–193 and 260–267.", true),
            Node("chiral", "chiral", "Chiral events", ChiralFormula(),
                "An event is chiral if no proper orthochronous Lorentz matrix and no independent pair permutations carry it to its parity image. "
                    + "This is the characterization in prelims.tex:240–243 and 265–268, extended as a predicate on the ambient event type.", true),
            Node("all-events", "allEvents", "The full forward-cone event class", AllEventsFormula(),
                "Every one of the four entries belongs to the forward cone. With the common pair-permutation and Lorentz symmetries, this is the class of all (pq)(ab) events in prelims.tex:662–666. "
                    + "There is no additional momentum-conservation constraint.", true),
            Node("collision-events", "collisionEvents", "The collision event class", CollisionEventsFormula(),
                "A collision event is a forward-cone event for which the product of the squared masses of p and q is strictly less than the square of their Minkowski product. "
                    + "This is the collision condition of prelims.tex:433–443 and the class (pq) to (ab) plus X in prelims.tex:656–660.", true),
            Node("admissible", "admissible", "Continuous invariant parity-odd variables", AdmissibleFormula(),
                "The variable is real-valued, continuous on om, invariant under every allowed Lorentz matrix and both pair permutations at every event in om, and parity odd there. "
                    + "These are the first four requirements in goals.tex:1–10. No continuity or symmetry condition is imposed outside om.", true),
            Node("claim", "claim", "The two-variable obstruction", ClaimDefinitionFormula(),
                "For each of the full and collision event classes, any two admissible real variables vanish together at some chiral event. "
                    + "This expresses the lower-bound assertion of the minimality conjecture in introduction.tex:103–104: neither one nor two such variables can be sufficient. "
                    + "The one-variable case follows by taking both variables equal. The statement supplies no construction or sufficiency proof for a three-variable set.", true),
            Node("family", "family", "A sphere of four-particle events", FamilyFormula(),
                "For v on the unit sphere, write s, t and d for its three real coordinates and aa and bb for the indicated positive square roots. "
                    + "The first two momenta are fixed; the final two encode the sphere coordinates in their energies, transverse lengths and opposite longitudinal coordinates. "
                    + "The formula is defined on all of Euclidean three-space; its collision membership and chirality are used on the unit sphere.", false),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A common zero on a chiral event"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First consider the displayed family on the unit sphere. Its coordinates satisfy s² + t² + d² = 1, so s and t lie between minus one and one. "
                            + "The squared transverse lengths are 4+t and 4−t. Both energies 10+s and 10−s are positive, and the squared masses of the last two momenta are "
                            + "95+20s+2s²−t+t² and 95−20s+2s²+t+t², each at least 74. "
                            + "All four momenta therefore lie in the forward cone. The first two squared masses are 899 and 399 and their Minkowski product is 601; "
                            + "899 times 399 is strictly less than 601 squared. Every event of the sphere is consequently a collision event. "
                            + "Each coordinate depends continuously on v, including the square roots, so the family is continuous.")),
                    Paragraph(Text(
                        "To establish chirality, suppose an allowed matrix lam and pair permutations carry such an event to its parity image. "
                            + "First let sigma fix the first pair and put h = eta times lam. Then h preserves eta, fixes p and q, and has determinant minus one. "
                            + "The two fixed vectors span the time-longitudinal plane. Solving their coordinate equations and using preservation of eta shows that h fixes this plane pointwise and has no mixed entries with the transverse plane. "
                            + "If tau fixes the second pair, h fixes the two nonzero independent transverse vectors (aa,0) and (0,bb). "
                            + "Its remaining block is the identity, so h is the identity, contradicting its determinant. "
                            + "If tau exchanges the second pair, the time and longitudinal coordinates give s = d = 0. Preservation of the Minkowski squared norm gives aa = bb; "
                            + "their squared values then give t = 0, contradicting the unit-sphere equation. "
                            + "Finally, if sigma exchanges p and q, preservation of their squared norms would equate 899 and 399. This rules out every pair of permutations.")),
                    Paragraph(Text(
                        "Direct coordinate comparison gives the antipodal identity below: rotation, together with exchange of the last pair, carries the parity image of the event at v to the event at −v.")),
                    new DocumentBlock.DisplayFormula(AntipodalFormula()),
                    Paragraph(Text(
                        "Whenever collisionEvents is contained in om, composing either admissible variable with the family is continuous on the sphere. "
                            + "The closed expression below sends each pair of real variables to its complex-valued pullback. For admissible variables this pullback is continuous on the sphere. "
                            + "Parity preserves the forward cone and the collision inequality, hence preserves both event domains. "
                            + "The displayed rotation preserves eta, has determinant one and has positive time-time entry; its determinant follows by writing it as the spatial coordinate exchange times eta. "
                            + "Invariance applied at the parity image, followed by parity oddness and the antipodal identity, makes each real pullback odd. "
                            + "The same holds after the explicit inclusions into the complex numbers, so their displayed complex combination is odd.")),
                    new DocumentBlock.DisplayFormula(ComplexMapFormula()),
                    Paragraph(Text(
                        "For om equal to allEvents, use the inclusion of collisionEvents into allEvents. Apply the planar odd-map zero theorem, Borsuk's Satz II (1933) for n=2, reviewed in Library note D5/L/Topology/borsuk1933spheres, to the complex combination and obtain a unit vector where it vanishes. "
                            + "The family event there is in om and is chiral; taking real and imaginary parts gives f₁ = f₂ = 0. "
                            + "For om equal to collisionEvents, use the identity inclusion and repeat the same argument. These are the two possibilities for om, which proves the full assertion."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula, string prose, bool literature) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula EventFormula() => Equal(Local("event"), Arrow(FinOf(D(4)), VectorType()));
    private static Formula EtaFormula() => Equal(Local("eta"), At(Qualified("Matrix", "diagonal"),
        Vec(D(1), Negative(D(1)), Negative(D(1)), Negative(D(1)))));
    private static Formula RotationFormula() => Equal(Local("rotation"), Seq(Bang, Bang, OpenBracket,
        Row(D(1), D(0), D(0), D(0)), Semi, Sp,
        Row(D(0), D(0), Negative(D(1)), D(0)), Semi, Sp,
        Row(D(0), Negative(D(1)), D(0), D(0)), Semi, Sp,
        Row(D(0), D(0), D(0), Negative(D(1))), CloseBracket));
    private static Formula MinkowskiFormula() => All("x", VectorType(), All("y", VectorType(),
        Equal(LocalCall("minkowski", X("x"), X("y")),
            Subtract(Subtract(Subtract(Multiply(Coordinate("x", 0), Coordinate("y", 0)),
                Multiply(Coordinate("x", 1), Coordinate("y", 1))),
                Multiply(Coordinate("x", 2), Coordinate("y", 2))),
                Multiply(Coordinate("x", 3), Coordinate("y", 3))))));
    private static Formula ForwardConeFormula() => Equal(Local("forwardCone"), SetOf("x", VectorType(),
        And(LE(D(0), Coordinate("x", 0)), LE(Add(Add(Square(Coordinate("x", 1)),
            Square(Coordinate("x", 2))), Square(Coordinate("x", 3))), Square(Coordinate("x", 0))))));
    private static Formula ProperFormula() => Equal(Local("properOrthochronous"), SetOf("lam", MatrixType(),
        And(Equal(Multiply(Multiply(At(Qualified("Matrix", "transpose"), X("lam")), Local("eta")), X("lam")), Local("eta")),
            And(Equal(At(Qualified("Matrix", "det"), X("lam")), D(1)), LT(D(0), At(X("lam"), D(0), D(0)))))));
    private static Formula ParityVectorFormula() => All("x", VectorType(),
        Equal(LocalCall("parityVector", X("x")), Vec(Coordinate("x", 0), Negative(Coordinate("x", 1)),
            Negative(Coordinate("x", 2)), Negative(Coordinate("x", 3)))));
    private static Formula ParityFormula() => All("x", EventType(), Equal(LocalCall("parity", X("x")),
        Vec(LocalCall("parityVector", Coordinate("x", 0)), LocalCall("parityVector", Coordinate("x", 1)),
            LocalCall("parityVector", Coordinate("x", 2)), LocalCall("parityVector", Coordinate("x", 3)))));
    private static Formula ActFormula() => All("lam", MatrixType(), All("sigma", PermType(), All("tau", PermType(),
        All("x", EventType(), Equal(LocalCall("act", X("lam"), X("sigma"), X("tau"), X("x")),
            Vec(ActEntry("castAdd", "sigma", 0), ActEntry("castAdd", "sigma", 1),
                ActEntry("natAdd", "tau", 0), ActEntry("natAdd", "tau", 1)))))));
    private static Formula ActEntry(string embedding, string permutation, byte index) =>
        At(Qualified("Matrix", "mulVec"), X("lam"), At(X("x"),
            At(Qualified("Fin", embedding), D(2), At(X(permutation), D(index)))));
    private static Formula ChiralFormula() => All("x", EventType(), IffOf(LocalCall("chiral", X("x")),
        new Formula.Not(Parenthesized(Some("lam", MatrixType(), And(Member(X("lam"), Local("properOrthochronous")),
            Some("sigma", PermType(), Some("tau", PermType(),
                Equal(LocalCall("act", X("lam"), X("sigma"), X("tau"), X("x")), LocalCall("parity", X("x")))))))))));
    private static Formula AllEventsFormula() => Equal(Local("allEvents"), SetOf("x", EventType(),
        All("i", FinOf(D(4)), Member(At(X("x"), X("i")), Local("forwardCone")))));
    private static Formula CollisionEventsFormula() => Equal(Local("collisionEvents"), SetOf("x", EventType(),
        And(Member(X("x"), Local("allEvents")), LT(Multiply(MinkowskiAt(0, 0), MinkowskiAt(1, 1)),
            Square(MinkowskiAt(0, 1))))));
    private static Formula MinkowskiAt(byte i, byte j) => LocalCall("minkowski", Coordinate("x", i), Coordinate("x", j));
    private static Formula AdmissibleFormula()
    {
        Formula invariance = All("x", EventType(), Imp(Member(X("x"), X("om")),
            All("lam", MatrixType(), Imp(Member(X("lam"), Local("properOrthochronous")),
                All("sigma", PermType(), All("tau", PermType(),
                    Equal(At(X("f"), LocalCall("act", X("lam"), X("sigma"), X("tau"), X("x"))),
                        At(X("f"), X("x")))))))));
        Formula oddness = All("x", EventType(), Imp(Member(X("x"), X("om")),
            Equal(At(X("f"), LocalCall("parity", X("x"))), Negative(At(X("f"), X("x"))))));
        return All("om", SetType(EventType()), All("f", VariableType(),
            IffOf(LocalCall("admissible", X("om"), X("f")),
                And(At(Qualified("ContinuousOn"), X("f"), X("om")), And(invariance, oddness)))));
    }
    private static Formula ClaimDefinitionFormula() => IffOf(Local("claim"), ClaimFormula());
    private static Formula ClaimFormula() => All("om", SetType(EventType()),
        Imp(Member(X("om"), new Formula.SetLiteral([Local("allEvents"), Local("collisionEvents")])),
            All("f₁", VariableType(), All("f₂", VariableType(),
                Imp(LocalCall("admissible", X("om"), X("f₁")), Imp(LocalCall("admissible", X("om"), X("f₂")),
                    Some("x", EventType(), And(Member(X("x"), X("om")), And(LocalCall("chiral", X("x")),
                        And(Equal(At(X("f₁"), X("x")), D(0)), Equal(At(X("f₂"), X("x")), D(0))))))))))));
    private static Formula FamilyFormula() => All("v", EuclideanType(), Equal(LocalCall("family", X("v")),
        LetIn("s", Coordinate("v", 0),
        LetIn("t", Coordinate("v", 1),
        LetIn("d", Coordinate("v", 2),
        LetIn("aa", At(Qualified("Real", "sqrt"), Add(D(4), X("t"))),
        LetIn("bb", At(Qualified("Real", "sqrt"), Subtract(D(4), X("t"))),
            Vec(Vec(D(3, 0), D(0), D(0), D(1)), Vec(D(2, 0), D(0), D(0), Negative(D(1))),
                Vec(Add(D(1, 0), X("s")), X("aa"), D(0), X("d")),
                Vec(Subtract(D(1, 0), X("s")), D(0), X("bb"), Negative(X("d")))))))))));
    private static Formula AntipodalFormula() => All("v", EuclideanType(),
        Equal(LocalCall("family", Negative(X("v"))), LocalCall("act", Local("rotation"), Typed(D(1), PermType()),
            At(Qualified("Equiv", "swap"), Typed(D(0), FinOf(D(2))), Typed(D(1), FinOf(D(2)))),
            LocalCall("parity", LocalCall("family", X("v"))))));
    private static Formula ComplexMapFormula() => LambdaOf("f₁", VariableType(), LambdaOf("f₂", VariableType(),
        LambdaOf("v", EuclideanType(), Add(At(Qualified("Complex", "ofReal"), At(X("f₁"), LocalCall("family", X("v")))),
            Multiply(At(Qualified("Complex", "ofReal"), At(X("f₂"), LocalCall("family", X("v")))), Qualified("Complex", "I"))))));

    private static Formula X(string name) => name switch
    {
        "f₁" => new Formula.Subscript(F.Id("f"), D(1)),
        "f₂" => new Formula.Subscript(F.Id("f"), D(2)),
        _ => F.Id(name),
    };
    private static Formula Local(string name) => Qualified("D5", "S3", "Geometry", "Lorentz", "ChiralEventParityMinimality", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula VectorType() => Arrow(FinOf(D(4)), Reals());
    private static Formula EventType() => Local("event");
    private static Formula SetType(Formula type) => At(Qualified("Set"), type);
    private static Formula MatrixType() => At(Qualified("Matrix"), FinOf(D(4)), FinOf(D(4)), Reals());
    private static Formula PermType() => At(Qualified("Equiv", "Perm"), FinOf(D(2)));
    private static Formula VariableType() => Arrow(EventType(), Reals());
    private static Formula EuclideanType() => At(Qualified("EuclideanSpace"), Reals(), FinOf(D(3)));
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(Parenthesized(left), Parenthesized(right));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula LetIn(string name, Formula value, Formula body) =>
        Seq(Operatorname, Grp(F.Id("let")), Sp, Typed(X(name), Reals()), Sp, Colon, Eq, Sp, value,
            Sp, Operatorname, Grp(F.Id("in")), Sp, Parenthesized(body));
    private static Formula SetOf(string name, Formula type, Formula body) =>
        Seq(OpenBrace, X(name), Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula Coordinate(string name, byte index) => At(X(name), D(index));
    private static Formula Row(Formula a, Formula b, Formula c, Formula d) => Seq(a, Comma, Sp, b, Comma, Sp, c, Comma, Sp, d);
    private static Formula Vec(Formula a, Formula b, Formula c, Formula d) => Seq(Bang, OpenBracket, Row(a, b, c, d), CloseBracket);
    private static Formula Negative(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula Square(Formula value) => new Formula.Power(Parenthesized(value), D(2));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
