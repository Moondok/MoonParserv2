#include "./include/mainwindow.h"
#include ".\\include\\util.h"

MainWindow::MainWindow(QWidget *parent)
    : QMainWindow(parent)
{
    this->setFixedSize(WIDTH,HEIGHT);

    label.setParent(this);
    label.setText("welcome to MoonParserV2");
    label.setFont(QFont("Consolas",35,18));
    label.setFixedSize(1000,200);
    label.move(150,300);

    startBtn=new QPushButton("START",this);
    startBtn->setFixedSize(150,60);
    startBtn->move(300,600);

    exitBtn=new QPushButton("EXIT",this);
    exitBtn->setFixedSize(150,60);
    exitBtn->move(750,600);

    connect(startBtn,&QPushButton::clicked,this,[=](){
        qDebug()<<"h";

        rule_page* rulepage= new rule_page(this);
        this->hide();
        rulepage->show();

        connect(rulepage,&rule_page::return_signal,this,[=](){
            rulepage->hide();
            this->show();
        });
        //func_page->show();
    });

    connect(exitBtn,&QPushButton::clicked,this,&QMainWindow::close);

}

MainWindow::~MainWindow()
{
}

