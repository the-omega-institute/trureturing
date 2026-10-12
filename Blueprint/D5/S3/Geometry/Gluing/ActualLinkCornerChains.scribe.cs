using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Gluing;

internal sealed class ActualLinkCornerChainsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Gluing/ActualLinkCornerChains.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original affine link chains: exact interior and positive-side classes, strict-region saturation and restriction.",
        H("Actual guarded corner chains"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-link-faceperm"),
                DeclarationHandle.Create(Prefix + "facePerm"), H("The original whole-face permutations"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("facePerm"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four rows are p=(3,0,1,2), q=(3,2,0,1), q inverse and p inverse. The private frozen_face_data proof compares these whole-face maps with the published facePair and slotMap on each actual face slot."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-reverseface"),
                DeclarationHandle.Create(Prefix + "reverseFace"), H("Inverse omitted faces"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("reverseFace"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Faces 0 and 3 are paired; faces 1 and 2 are paired."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-faceword"),
                DeclarationHandle.Create(Prefix + "faceWord"), H("The source group words"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("faceWord"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The source-to-target words are u, v, v inverse, u inverse, in omitted-face order. Multiplication retains the published right-action convention."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-raw"),
                DeclarationHandle.Create(Prefix + "Raw"), H("Tagged barycentric coordinates"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("Raw"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A raw representative has an actual corner (omega,j) and four real barycentric coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-carrier"),
                DeclarationHandle.Create(Prefix + "Carrier"), H("The complete original corner triangle"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("Carrier"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coordinate at j is zero, every coordinate is nonnegative, and their sum is one. The actual corner label is the fixed nu from the frozen Pairing quotient. Boundary ties remain in this closed carrier."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-point"),
                DeclarationHandle.Create(Prefix + "Point"), H("The actual carrier subtype"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("Point"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Representatives carry all closed-carrier conditions and the same actual corner-class tag."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-move"),
                DeclarationHandle.Create(Prefix + "move"), H("Original affine face transport"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("move"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transport the sheet by the exact source word, the omitted corner by the whole-face permutation, and the coordinate vector by its inverse. No endpoints are sorted."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-pairedpoint"),
                DeclarationHandle.Create(Prefix + "pairedPoint"), H("A permitted affine image in the same actual corner class"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("pairedPoint"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The input requires f different from the omitted corner j. The carrier proof directly consumes the published actual_step helper at its original owner, after extending the original face-slot table. The sum and coordinate conditions are preserved by the whole-face permutation. This definition constructs the affine image even away from a side; the Step relation separately imposes the zero guard."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-step"),
                DeclarationHandle.Create(Prefix + "Step"), H("Only the original guarded link generators"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("Step"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A step requires f different from j and beta(f)=0, and its target is the displayed affine image. The identically zero omitted-corner coordinate creates no fourth side."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-related"),
                DeclarationHandle.Create(Prefix + "Related"), H("The full original affine equivalence closure"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("Related"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take EqvGen of Step on the entire closed carrier. No chart region, assumed cycle or radial-map kernel defines this relation."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-dart"),
                DeclarationHandle.Create(Prefix + "Dart"), H("Ordered endpoint data"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("Dart"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The raw ordered occurrence is ((omega,j),k). Actual corner neighborhoods have j different from k because beta(j)=0 and beta(k)>1/2. The data type retains every order, including (3,0)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-dartmove"),
                DeclarationHandle.Create(Prefix + "dartMove"), H("The same whole-face transport on ordered endpoints"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("dartMove"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both j and k move by the actual face permutation; the sheet moves by the actual word."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-dartstep"),
                DeclarationHandle.Create(Prefix + "DartStep"), H("Original oriented edge-incidence transport"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("DartStep"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A dart step may use only a face omitting neither endpoint. This is a generated incidence relation, not an assumed cyclic enumeration."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-dartrelated"),
                DeclarationHandle.Create(Prefix + "DartRelated"), H("The actual ordered-dart component"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("DartRelated"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The equivalence closure is generated by the actual guarded endpoint moves. This delivery does not enumerate its component by Fin(3r)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-neighborhood"),
                DeclarationHandle.Create(Prefix + "Neighborhood"), H("Strict corner regions from an actual endpoint component"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("Neighborhood"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A representative is selected when some beta(k)>1/2 and its ordered dart is in the actual component of the selected seed. The strict inequality excludes boundary ties from this region while retaining them in Carrier. This delivery proves saturation and chain reflection; it does not yet prove openness or a disk coordinate."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-interior"),
                DeclarationHandle.Create(Prefix + "Interior"), H("Interior coordinates"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("Interior"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every non-omitted coordinate is nonzero. On the nonnegative closed carrier this means each of those three coordinates is positive."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-edgepoint"),
                DeclarationHandle.Create(Prefix + "EdgePoint"), H("A unique active side"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("EdgePoint"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exactly one non-omitted coordinate is zero. The other two are nonzero and, on this carrier, positive."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-actual-guarded-point-analysis"),
                DeclarationHandle.Create(Prefix + "actual_guarded_point_analysis"), H("Source-specific normal forms and full-chain restriction"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("actual_guarded_point_analysis"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every group, arbitrary right action, u and v, actual corner class nu, and original representatives x and y: an interior x has singleton class; an EdgePoint has exactly x and its distinct original paired image as its class; every strict component neighborhood is invariant under the full EqvGen; and restriction to that neighborhood reflects the full relation. The positive-side proof constructs a two-point invariant from the unique active guard and inverse pairing. It then inducts through all four EqvGen constructors. Saturation is established before the restriction proof, whose transitive case explicitly transports membership to the intermediate representative. These are new original-carrier deductions, not applications of an assumed cycle or assumed relation correspondence. The helpers are consumed on these live proof paths. The remaining local obligations are the four minimal point-period Fin(3r) enumerations, the exact origin-cycle and fan-seam correspondence, openness with the actual quotient-subspace topology, the supplied fan radial chart at the same actual vertex, and the geometric truncation-slice chain and topology comparison. Global orientability, genus, marked-manifold realization and metric statements remain outside this result. No external novelty is claimed."))),
                DescribeRole.Theorem))));

    private static Formula FormulaFor(string name)
    {
        var x = F.Id("x"); var y = F.Id("y"); var d = F.Id("d");
        var f = F.Id("f"); var g = F.Id("g"); var k = F.Id("k"); var i = F.Id("i");
        var u = F.Id("u"); var v = F.Id("v"); var nu = F.Id("nu");
        var omega = F.Id("Omega"); var fin4 = Call("Fin", F.D(4));
        var point = Call("Point", u, v, nu);
        var corner = Call("corner", x);
        var j = Call("second", corner);
        var betaF = Call("coordinate", x, f);
        var perm = Call("facePerm", f);
        var paired = Call("pairedPoint", u, v, x, f);
        var related = Call("Related", u, v, x, y);
        var neighborhood = Call("Neighborhood", u, v, d);
        Formula X(Formula body) => All("x", point, body);
        Formula XY(Formula body) => X(All("y", point, body));
        return name switch
        {
            "facePerm" => All("f", fin4, All("i", fin4,
                Eq(Call("facePerm", f, i), Call("lookup",
                    Tuple(Tuple(F.D(3),F.D(0),F.D(1),F.D(2)),
                        Tuple(F.D(3),F.D(2),F.D(0),F.D(1)),
                        Tuple(F.D(2),F.D(3),F.D(1),F.D(0)),
                        Tuple(F.D(1),F.D(2),F.D(3),F.D(0))), f, i)))),
            "reverseFace" => All("f", fin4, Eq(Call("reverseFace", f),
                Call("lookup", Tuple(F.D(3),F.D(2),F.D(1),F.D(0)), f))),
            "faceWord" => Scope(All("f", fin4, Eq(Call("faceWord",u,v,f),
                Call("lookup", Tuple(u,v,Call("inverse",v),Call("inverse",u)), f)))),
            "Raw" => All("Omega",F.Id("Type"),
                Eq(Call("Raw",omega), Product(Product(omega,fin4),Call("Functions",fin4,F.Id("R"))))),
            "Carrier" => Scope(All("x",Call("Raw",omega),
                Iff(In(x,Call("Carrier",u,v,nu)), And(
                    Eq(Call("coordinate",x,j),F.D(0)),
                    All("i",fin4,Le(F.D(0),Call("coordinate",x,i))),
                    Eq(Call("sumCoordinates",x),F.D(1)),
                    Eq(Call("label",Call("pairing",u,v),corner),nu))))),
            "Point" => Scope(Eq(point,Call("Subtype",Call("Carrier",u,v,nu)))),
            "move" => Scope(All("f",fin4,All("x",Call("Raw",omega),
                Eq(Call("move",u,v,f,x),
                    Pair(Pair(Call("act",Call("first",corner),Call("faceWord",u,v,f)),
                        Call("apply",perm,j)),Call("pullback",perm,Call("coordinates",x))))))),
            "pairedPoint" => Scope(X(All("f",fin4,Implies(Ne(f,j),
                Eq(Call("value",paired),Call("move",u,v,f,Call("value",x))))))),
            "Step" => Scope(XY(Iff(Call("Step",u,v,x,y),Exists("f",fin4,
                And(Ne(f,j),Eq(betaF,F.D(0)),
                    Eq(Call("value",y),Call("move",u,v,f,Call("value",x)))))))),
            "Related" => Scope(XY(Iff(related,Call("EqvGen",Call("Step",u,v),x,y)))),
            "Dart" => All("Omega",F.Id("Type"),
                Eq(Call("Dart",omega),Product(Product(omega,fin4),fin4))),
            "dartMove" => Scope(All("d",Call("Dart",omega),All("f",fin4,
                Eq(Call("dartMove",u,v,f,d),
                    Pair(Pair(Call("act",Call("sheet",d),Call("faceWord",u,v,f)),
                        Call("apply",perm,Call("firstEndpoint",d))),
                        Call("apply",perm,Call("secondEndpoint",d))))))),
            "DartStep" => Scope(All("d",Call("Dart",omega),All("e",Call("Dart",omega),
                Iff(Call("DartStep",u,v,d,F.Id("e")),Exists("f",fin4,
                    And(Ne(f,Call("firstEndpoint",d)),Ne(f,Call("secondEndpoint",d)),
                        Eq(F.Id("e"),Call("dartMove",u,v,f,d)))))))),
            "DartRelated" => Scope(All("d",Call("Dart",omega),All("e",Call("Dart",omega),
                Iff(Call("DartRelated",u,v,d,F.Id("e")),
                    Call("EqvGen",Call("DartStep",u,v),d,F.Id("e")))))),
            "Neighborhood" => Scope(All("d",Call("Dart",omega),X(
                Iff(In(x,neighborhood),Exists("k",fin4,And(
                    Lt(new Formula.Fraction(F.D(1),F.D(2)),Call("coordinate",x,k)),
                    Call("DartRelated",u,v,d,Pair(corner,k)))))))),
            "Interior" => Scope(X(Iff(Call("Interior",x),
                All("f",fin4,Implies(Ne(f,j),Ne(betaF,F.D(0))))))),
            "EdgePoint" => Scope(X(All("f",fin4,Iff(Call("EdgePoint",x,f),
                And(Ne(f,j),Eq(betaF,F.D(0)),All("g",fin4,
                    Implies(And(Ne(g,j),Eq(Call("coordinate",x,g),F.D(0))),Eq(g,f)))))))),
            "actual_guarded_point_analysis" => Scope(XY(And(
                Implies(Call("Interior",x),Iff(related,Eq(y,x))),
                All("f",fin4,Implies(Call("EdgePoint",x,f),
                    And(Ne(paired,x),Iff(related,Or(Eq(y,x),Eq(y,paired)))))),
                All("d",Call("Dart",omega),Implies(related,
                    Iff(In(x,neighborhood),In(y,neighborhood)))),
                All("d",Call("Dart",omega),Implies(And(In(x,neighborhood),In(y,neighborhood)),
                    Iff(related,Call("EqvGen",Call("StepRestrictedTo",u,v,neighborhood),
                        Call("subtype",x),Call("subtype",y)))))))),
            _ => throw new System.ArgumentOutOfRangeException(nameof(name))
        };
    }
    private static Formula Scope(Formula body) =>
        All("G",F.Id("Group"),All("Omega",Call("RightAction",F.Id("G")),
            All("u",F.Id("G"),All("v",F.Id("G"),
                All("nu",Call("Vertex",Call("pairing",F.Id("u"),F.Id("v"))),body)))));
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(name),domain,body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(name),domain,body);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name),[.. args]);
    private static Formula Pair(Formula a, Formula b) => Tuple(a,b);
    private static Formula Tuple(params Formula[] xs)
    {
        var parts = new System.Collections.Generic.List<Formula> { F.Open };
        for (var i = 0; i < xs.Length; i++)
        {
            if (i > 0) { parts.Add(F.Comma); parts.Add(F.Sp); }
            parts.Add(xs[i]);
        }
        parts.Add(F.Close);
        return F.Seq([.. parts]);
    }
    private static Formula Product(Formula a, Formula b) => F.Seq(a,F.Sp,F.Times,F.Sp,b);
    private static Formula And(params Formula[] xs)
    {
        var r = xs[^1];
        for (var i = xs.Length-2; i >= 0; i--) r = new Formula.Logic(xs[i],FormulaLogicOperator.And,r);
        return r;
    }
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a, Formula b) => F.Seq(a,F.Sp,F.Neq,F.Sp,b);
    private static Formula In(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.MemberOf,b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Or,b);
}
