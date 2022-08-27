MACHINE           LIBRARY

SETS              BOOK; USER; AUTHOR; YEAR; CATEGORY = {Fantasy, SciFi, Mystery, Romance}

VARIABLES         books, users, users_has_login, users_member, author, publish_in, borrowed, has_borrowed, reserved, book_category


INVARIANT         books : POW(BOOK) & 
                  users : POW(USER) & 
		  users_has_login : POW(USER) & 
		  users_member : POW(USER) & 
		  author: BOOK <-> AUTHOR &
		  publish_in: BOOK <-> YEAR &
		  book_category :  CATEGORY<-> BOOK &
       		  borrowed : POW(BOOK) &
     		  has_borrowed: USER <-> POW(BOOK) &
		  reserved: BOOK +-> USER

INITIALISATION    books := {};
		  book_category := {};
                  users := {};
		  users_has_login := {};
		  users_member := {};
		  author := {};
		  publish_in := {};
		  borrowed :={};
		  reserved := {};
   		  has_borrowed:= {}

OPERATIONS
  add_book(kk, aa, yy) = PRE kk:BOOK & kk /: books & aa : AUTHOR & yy:YEAR THEN books := books \/ {kk}; author := author \/ {kk |-> aa}; publish_in := publish_in \/ {kk |-> yy} END;

  set_book_category(kk, cc) = PRE kk:BOOK & kk: books & cc: CATEGORY & cc |-> kk/:book_category THEN book_category := book_category \/ {cc |-> kk} END;

  delete_book(kk) = PRE kk : books& kk/: borrowed THEN books := books - {kk}; author := {kk} <<| author; publish_in := {kk} <<| publish_in ; book_category := book_category |>> {kk}; IF kk: dom(reserved) THEN reserved:= {kk} <<| reserved END  END;

  add_user(rr) = PRE rr:USER & rr /: users THEN users := users \/ {rr} ;  has_borrowed := has_borrowed \/ {rr |-> {}} END;

  delete_user(rr) = PRE rr : users & (has_borrowed={}or has_borrowed(rr)={}) THEN users := users - {rr}; has_borrowed:={rr} <<| has_borrowed ; IF rr: ran(reserved) THEN reserved:= reserved |>> {rr} ELSE reserved:= reserved END END;

  user_login (uu) = PRE uu : users & uu/: users_has_login THEN users_has_login := users_has_login \/ {uu} END;

  buy_member (uu) = PRE uu : users & uu: users_has_login & uu: users_has_login & uu/: users_member THEN users_member := users_member \/ {uu} END;

  user_logout (uu) = PRE uu : users & uu: users_has_login THEN users_has_login := users_has_login - {uu} END;

  borrow_book(kk,uu) = PRE kk:BOOK & kk:books & kk/: borrowed & uu:users & uu:users_has_login & ( kk/: dom(reserved) or (kk: dom(reserved) & reserved(kk)=uu)) & ( uu : users_member or (uu /: users_member & card(has_borrowed(uu))=0))THEN borrowed := borrowed \/ {kk}; has_borrowed(uu) := has_borrowed(uu)\/{kk}; IF kk: dom(reserved) THEN reserved:= {kk} <<| reserved END END;

  return_book(kk,uu) = PRE kk:BOOK & kk:books & kk: borrowed & kk:has_borrowed(uu) & uu:users & uu:users_has_login THEN borrowed := borrowed - {kk}; has_borrowed(uu) := has_borrowed(uu)-{kk} END;

  return_all_book(uu) = PRE uu:users & card(has_borrowed(uu))>0 & uu:users_has_login THEN borrowed := borrowed - has_borrowed(uu); has_borrowed(uu) := {} END;

  reserve_book(kk,uu) = PRE kk:BOOK & kk:books & kk: borrowed & kk /: has_borrowed(uu) & uu:users & uu:users_has_login & kk/: dom(reserved)  & uu:users_member THEN reserved := reserved \/ {kk |-> uu}END;

  output <-- get_all_available_books = PRE books /= {} THEN output:= books - borrowed - dom(reserved) END;

  output <-- search_author(aa) = PRE books /= {} & aa:AUTHOR THEN output:=author |> {aa} END;

  output <-- search_year(yy) = PRE books /= {} & yy:YEAR THEN output:=publish_in |> {yy} END;

  output <-- get_book_of_the_day = ANY item WHERE item : books THEN output:= item END;

  output <-- search_category(cc) = PRE books /= {} & cc:CATEGORY THEN output:= {cc}<| book_category  END;

  output <-- search_book(bb) = PRE books /= {} THEN IF bb: books THEN output:= {bb} ELSE output:= {}  END END


END
