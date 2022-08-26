MACHINE           EKS
/* This B Machine models a simplified electronic key system.
*/
SETS              BOOK; USER; AUTHOR; YEAR; CATEGORY = {Fantasy, SciFi, Mystery, Romance}

VARIABLES         books, users, users_has_login, users_member, author, publish_in, borrowed, has_borrowed, reserved, book_category


INVARIANT         books : POW(BOOK) & 
		  book_category :  CATEGORY<-> BOOK &
                  users : POW(USER) & 
		  users_has_login : POW(USER) & 
		  users_member : POW(USER) & 
		  author: BOOK <-> AUTHOR &
		  publish_in: BOOK <-> YEAR &
       		  borrowed : POW(BOOK) &
     		  has_borrowed: USER <-> POW(BOOK) &
		  reserved: BOOK +-> USER

INITIALISATION    books := {};
		  book_category := {};
                  users := {};
		  users_has_login := {};
		  users_member := {};
		  author := BOOK * {};
		  publish_in := BOOK * {};
		  borrowed :={};
		  reserved := {};
   		  has_borrowed:= {}

OPERATIONS
  addbook(kk, aa, yy) = PRE kk:BOOK & kk /: books & aa : AUTHOR & yy:YEAR THEN books := books \/ {kk}; author := author \/ {kk |-> aa}; publish_in := publish_in \/ {kk |-> yy} END;

  setbookcategory(kk, cc) = PRE kk:BOOK & kk: books & cc: CATEGORY & cc |-> kk/:book_category THEN book_category := book_category \/ {cc |-> kk} END;

  deletebook(kk) = PRE kk : books& kk/: borrowed THEN books := books - {kk}; author := {kk} <<| author; publish_in := {kk} <<| publish_in ; book_category := book_category |>> {kk}; IF kk: dom(reserved) THEN reserved:= {kk} <<| reserved END  END;

  adduser(rr) = PRE rr:USER & rr /: users THEN users := users \/ {rr} ;  has_borrowed := has_borrowed \/ {rr |-> {}} END;

  deleteuser(rr) = PRE rr : users & (has_borrowed={}or has_borrowed(rr)={}) THEN users := users - {rr}; has_borrowed:={rr} <<| has_borrowed ; IF rr: ran(reserved) THEN reserved:= reserved |>> {rr} ELSE reserved:= reserved END END;

  userlogin (uu) = PRE uu : users & uu/: users_has_login THEN users_has_login := users_has_login \/ {uu} END;

  buymember (uu) = PRE uu : users & uu: users_has_login & uu: users_has_login & uu/: users_member THEN users_member := users_member \/ {uu} END;

  userlogout (uu) = PRE uu : users & uu: users_has_login THEN users_has_login := users_has_login - {uu} END;

  borrowbook(kk,uu) = PRE kk:BOOK & kk:books & kk/: borrowed & uu:users & uu:users_has_login & ( kk/: dom(reserved) or (kk: dom(reserved) & reserved(kk)=uu)) & ( uu : users_member or (uu /: users_member & card(has_borrowed(uu))=0))THEN borrowed := borrowed \/ {kk}; has_borrowed(uu) := has_borrowed(uu)\/{kk}; IF kk: dom(reserved) THEN reserved:= {kk} <<| reserved END END;

  returnbook(kk,uu) = PRE kk:BOOK & kk:books & kk: borrowed & kk:has_borrowed(uu) & uu:users & uu:users_has_login THEN borrowed := borrowed - {kk}; has_borrowed(uu) := has_borrowed(uu)-{kk} END;

  returnallbook(uu) = PRE uu:users & card(has_borrowed(uu))>0 & uu:users_has_login THEN borrowed := borrowed - has_borrowed(uu); has_borrowed(uu) := {} END;

  reservebook(kk,uu) = PRE kk:BOOK & kk:books & kk: borrowed & kk /: has_borrowed(uu) & uu:users & uu:users_has_login & kk/: dom(reserved)  & uu:users_member THEN reserved := reserved \/ {kk |-> uu}END;

  output <-- Get_all_available_books = PRE books /= {} THEN output:= books - borrowed - dom(reserved) END;

  output <-- Search_author(aa) = PRE books /= {} & aa:AUTHOR THEN output:=author |> {aa} END;

  output <-- Search_year(yy) = PRE books /= {} & yy:YEAR THEN output:=publish_in |> {yy} END;

  output <-- Get_book_of_the_day = ANY item WHERE item : books THEN output:= item END;

  output <-- Search_category(cc) = PRE books /= {} & cc:CATEGORY THEN output:= {cc}<| book_category  END;

  output <-- Search_book(bb) = PRE books /= {} THEN IF bb: books THEN output:= {bb} ELSE output:= {}  END END


END
