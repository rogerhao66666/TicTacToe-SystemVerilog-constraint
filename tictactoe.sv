`define N 5
typedef enum {CROSS = -1, EMPTY = 0, CIRCLE = 1} move_e;

class tictactoe;
  rand bit winning_game;
  rand bit draw_game;
  rand bit incomplete_game;
  rand int winD;
  
  rand bit [(2*`N+1):0] p1_win;
  rand bit [(2*`N+1):0] p2_win;
  
  rand move_e tic_toe [`N][`N];
  rand move_e tic_toe_t [`N][`N];
  
  rand int empty [`N][`N];
  rand int row_sum [`N];
  rand int col_sum [`N];
  rand int diag[`N];
  rand int diag_sum;
  rand int rdiag[`N];
  rand int rdiag_sum;
  rand int board_sum;
  rand int empty_sum_row [`N];
  rand int empty_sum;
  rand int intersection;
  
  //////////////////////////////////////
  //Top most decision - winning_game
  //////////////////////////////////////
  
  constraint tc1 {
    solve winning_game before p1_win, p2_win, draw_game, incomplete_game, winD;
    winning_game dist {0:=50, 1:=50};
  }
  
  
  /////////////////////////////////////////////////////////////
  //Second level decision - draw_game, 2d_win, incomplete_game
  /////////////////////////////////////////////////////////////
  
  constraint tc2 {
    solve draw_game before p1_win, p2_win;
    solve winD before p1_win, p2_win;
    draw_game dist {0:=50, 1:=50};
    winD inside {[0:4]};
    winD dist {0:=20, 1:=20, 2:=20, 3:=20, 4:=20};
    
    draw_game == 1 -> winning_game == 0;
    winning_game == 1 -> draw_game == 0;
    
    winning_game == 1 -> winD != 0;
    winning_game == 0 -> winD == 0;
    
    winning_game == 1 || draw_game == 1 -> incomplete_game == 0;
    winning_game == 0 && draw_game == 0 -> incomplete_game == 1;
  }
  
  /////////////////////////////////////////////////////////////
  //Third level decision - p1_wins, u2_wins
  /////////////////////////////////////////////////////////////
  
  constraint tc3 {
    solve p1_win before tic_toe, tic_toe_t, empty, row_sum, col_sum, diag, diag_sum, rdiag, rdiag_sum, board_sum, empty_sum, empty_sum_row;
    solve p2_win before tic_toe, tic_toe_t, empty, row_sum, col_sum, diag, diag_sum, rdiag, rdiag_sum, board_sum, empty_sum, empty_sum_row;
    
    $countones(p1_win)+$countones(p2_win) == winD;
    $countones(p1_win) == winD || $countones(p2_win) == winD;
    $countones(p1_win[`N-1:0]) <= 1;
    $countones(p1_win[2*`N-1:`N]) <= 1;
    $countones(p2_win[`N-1:0]) <= 1;
    $countones(p2_win[2*`N-1:`N]) <= 1;
    intersection inside {[0:`N-1]};
    solve intersection before p1_win, p2_win, draw_game, incomplete_game;
    
    if ((winning_game == 1) && (winD == 2)) {
      $countones(p1_win) == 2 ->
      ((p1_win[intersection] == 1) && (p1_win[intersection+`N] == 1)) ||
      ((p1_win[intersection] == 1) && (p1_win[2*`N] == 1)) ||
      ((p1_win[intersection] == 1) && (p1_win[2*`N+1] == 1)) ||
      ((`N%2==1) && (intersection == (`N-1)/2) && (p1_win[2*`N] == 1) && (p1_win[2*`N+1]));
      $countones(p2_win) == 2 ->
      ((p2_win[intersection] == 1) && (p2_win[intersection+`N] == 1)) ||
      ((p2_win[intersection] == 1) && (p2_win[2*`N] == 1)) ||
      ((p2_win[intersection] == 1) && (p2_win[2*`N+1] == 1)) ||
      ((`N%2==1) && (intersection == (`N-1)/2) && (p2_win[2*`N] == 1) && (p2_win[2*`N+1]));
    }
    
    if ((winning_game == 1) && (winD == 3)) {
      $countones(p1_win) == 3 ->
      ((p1_win[intersection] == 1) && (p1_win[intersection+`N] == 1) && (p1_win[2*`N] == 1)) ||
      ((p1_win[intersection] == 1) && (p1_win[intersection+`N] == 1) && (p1_win[2*`N+1] == 1)) ||
      ((`N%2==1) && (intersection == (`N-1)/2) && (p1_win[intersection] == 1) && (p1_win[2*`N] == 1) && (p1_win[2*`N+1] == 1)) ||
      ((`N%2==1) && (intersection == (`N-1)/2) && (p1_win[intersection+`N] == 1) && (p1_win[2*`N] == 1) && (p1_win[2*`N+1] == 1));
        
      $countones(p2_win) == 3 ->
      ((p2_win[intersection] == 1) && (p2_win[intersection+`N] == 1) && (p2_win[2*`N] == 1)) ||
      ((p2_win[intersection] == 1) && (p2_win[intersection+`N] == 1) && (p2_win[2*`N+1] == 1)) ||
      ((`N%2==1) && (intersection == (`N-1)/2) && (p2_win[intersection] == 1) && (p2_win[2*`N] == 1) && (p2_win[2*`N+1] == 1)) ||
      ((`N%2==1) && (intersection == (`N-1)/2) && (p2_win[intersection+`N] == 1) && (p2_win[2*`N] == 1) && (p2_win[2*`N+1] == 1));
     }
      
    if ((winning_game == 1) && (winD == 4)) {
      $countones(p1_win) == 4 ->
      ((`N%2==1) && (intersection == (`N-1)/2) && (p1_win[intersection] == 1) && (p1_win[intersection+`N] == 1) && (p1_win[2*`N] == 1) && (p1_win[2*`N+1] == 1));
      $countones(p2_win) == 4 ->
      ((`N%2==1) && (intersection == (`N-1)/2) && (p2_win[intersection] == 1) && (p2_win[intersection+`N] == 1) && (p2_win[2*`N] == 1) && (p2_win[2*`N+1] == 1));
    }
  }
   
  ////////////////////////////////////////////////////////////////////////
  //Fourth level decision - tic_tac, row_sum, col_sum, diag_sum, rdiag_sum
  ////////////////////////////////////////////////////////////////////////
    
  constraint tc4 {
    foreach (tic_toe[i,j]) {
      tic_toe_t[i][j] == tic_toe[j][i];
      i == j -> diag[i] == tic_toe[i][j];
      i+j == `N-1 -> rdiag[i] == tic_toe[i][j];
      tic_toe[i][j] == 0 -> empty[i][j] == 1;
      tic_toe[i][j] != 0 -> empty[i][j] == 0;
    }
      
    foreach (tic_toe[i]) {
      row_sum[i] == tic_toe[i].sum();
      col_sum[i] == tic_toe_t[i].sum();
    }
    
    diag_sum == diag.sum();
    rdiag_sum == rdiag.sum();
    
    board_sum == row_sum.sum();
    board_sum >= -1;
    board_sum <= 1;
    
    $countones(p1_win) > 0 -> board_sum <= 0;
    $countones(p2_win) > 0 -> board_sum >= 0;
    
    foreach (p1_win[i]) {
      if (i < `N) {
        (row_sum[i] == `N*CROSS) -> (p1_win[i] == 1);
        (p1_win[i] == 1) -> (row_sum[i] == `N*CROSS);
      }
      if (i < 2*`N && i >= `N) {
        (col_sum[i-`N] == `N*CROSS) -> (p1_win[i] == 1);
        (p1_win[i] == 1) -> (col_sum[i-`N] == `N*CROSS);
      }
      if (i == 2*`N) {
        (diag_sum == `N*CROSS) -> (p1_win[i] == 1);
        (p1_win[i] == 1) -> (diag_sum == `N*CROSS);
      }
      if (i == 2*`N+1) {
        (rdiag_sum == `N*CROSS) -> (p1_win[i] == 1);
        (p1_win[i] == 1) -> (rdiag_sum == `N*CROSS);
      }
    }
          
    foreach (p2_win[i]) {
      if (i < `N) {
        (row_sum[i] == `N*CIRCLE) -> (p2_win[i] == 1);
        (p2_win[i] == 1) -> (row_sum[i] == `N*CIRCLE);
      }
      if (i < 2*`N && i >= `N) {
        (col_sum[i-`N] == `N*CIRCLE) -> (p2_win[i] == 1);
        (p2_win[i] == 1) -> (col_sum[i-`N] == `N*CIRCLE);
      }
      if (i == 2*`N) {
        (diag_sum == `N*CIRCLE) -> (p2_win[i] == 1);
        (p2_win[i] == 1) -> (diag_sum == `N*CIRCLE);
      }
      if (i == 2*`N+1) {
        (rdiag_sum == `N*CIRCLE) -> (p2_win[i] == 1);
        (p2_win[i] == 1) -> (rdiag_sum == `N*CIRCLE);
      }
    }
    
    foreach (empty[i]) {
      empty_sum_row[i] == empty[i].sum();
    }
    empty_sum == empty_sum_row.sum();
      
    incomplete_game == 1 -> empty_sum > 0;
    draw_game == 1 -> empty_sum == 0;
      
  }
      
      
  function string get_sym (move_e move);
    string s;
    if (move == CROSS) s = "X";
    if (move == CIRCLE) s = "O";
    if (move == EMPTY) s = "_";
    return s;
  endfunction
      
  function void print ();
    string s;
    $display("Printing tic-tac");
    $display("winning_game=%0d, winD=%0d, draw_game=%0d incomplete_game=%h p1_wins=%b p2_wins=%b intersection=%0d\n", winning_game, winD, draw_game, incomplete_game, p1_win,p2_win, intersection );
    foreach (tic_toe[i]) begin
      s = "";
      foreach (tic_toe[i][j]) begin
        s = {s, " ", get_sym(tic_toe[i][j])};
      end
      $display(" %s",s);
    end
  endfunction

endclass
  
      
module automatic test;
  function void run ();
    tictactoe m_tictactoe = new();
    for (int i = 0; i < 10; i=i+1) begin
      $display("RANDOMIZE %0d", i);
      m_tictactoe.randomize() with {
        //winD == 4;
        winning_game == 1;
        //draw_game == 1;
        //incomplete_game == 1;
      };
      m_tictactoe.print();
    end
  endfunction
  initial begin
    run();
  end
endmodule
  